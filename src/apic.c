/*
 * APIC handling for legacy BIOS compatibility
 *
 * Modern UEFI systems boot with x2APIC enabled, which prevents legacy PIC
 * interrupts (like IRQ0 timer) from reaching the CPU. This module handles
 * the transition to a state compatible with legacy BIOS operation.
 *
 * References:
 * - Intel 64 Architecture x2APIC Specification
 * - EDK2 BaseXApicX2ApicLib
 * - Linux kernel x86/apic code
 */

#include <efi.h>
#include <stdbool.h>
#include <io.h>
#include <printf.h>

#include <uacpi/acpi.h>
#include <uacpi/tables.h>
#include <uacpi/uacpi.h>

/* MSR addresses */
#define MSR_IA32_APIC_BASE              0x1B
#define MSR_IA32_ARCH_CAPABILITIES      0x10A
#define MSR_IA32_XAPIC_DISABLE_STATUS   0xBD

/* IA32_APIC_BASE bits */
#define APIC_BASE_BSP                   (1ULL << 8)   /* Bootstrap processor */
#define APIC_BASE_EXTD                  (1ULL << 10)  /* x2APIC mode enable */
#define APIC_BASE_EN                    (1ULL << 11)  /* APIC global enable */
#define APIC_BASE_ADDR_MASK             0xFFFFFFFFFFFFF000ULL

/* IA32_ARCH_CAPABILITIES bits */
#define ARCH_CAP_XAPIC_DISABLE          (1ULL << 21)  /* IA32_XAPIC_DISABLE_STATUS exists */

/* IA32_XAPIC_DISABLE_STATUS bits */
#define XAPIC_DISABLE_LEGACY_DISABLED   (1ULL << 0)   /* xAPIC mode locked out */

/* x2APIC MSR addresses (base 0x800, offset = xAPIC offset >> 4) */
#define X2APIC_MSR_SIVR                 0x80F  /* Spurious Interrupt Vector (0xF0 >> 4) */
#define X2APIC_MSR_LVT_CMCI             0x82F  /* LVT CMCI (0x2F0 >> 4) */
#define X2APIC_MSR_LVT_TIMER            0x832  /* LVT Timer (0x320 >> 4) */
#define X2APIC_MSR_LVT_THERMAL          0x833  /* LVT Thermal (0x330 >> 4) */
#define X2APIC_MSR_LVT_PMC              0x834  /* LVT PMC (0x340 >> 4) */
#define X2APIC_MSR_LVT_LINT0            0x835  /* LVT LINT0 (0x350 >> 4) */
#define X2APIC_MSR_LVT_LINT1            0x836  /* LVT LINT1 (0x360 >> 4) */
#define X2APIC_MSR_LVT_ERROR            0x837  /* LVT Error (0x370 >> 4) */
#define X2APIC_MSR_VERSION              0x803  /* Version (0x030 >> 4) */
#define X2APIC_MSR_TPR                  0x808  /* Task Priority (0x080 >> 4) */

/* xAPIC MMIO offsets (from APIC base, typically 0xFEE00000) */
#define XAPIC_VERSION_OFFSET            0x030
#define XAPIC_TPR_OFFSET                0x080
#define XAPIC_SIVR_OFFSET               0x0F0
#define XAPIC_LVT_CMCI_OFFSET          0x2F0
#define XAPIC_LVT_TIMER_OFFSET         0x320
#define XAPIC_LVT_THERMAL_OFFSET       0x330
#define XAPIC_LVT_PMC_OFFSET           0x340
#define XAPIC_LVT_LINT0_OFFSET          0x350
#define XAPIC_LVT_LINT1_OFFSET          0x360
#define XAPIC_LVT_ERROR_OFFSET         0x370

/* LVT register bits */
#define LVT_VECTOR_MASK                 0xFF
#define LVT_DELIVERY_MODE_SHIFT         8
#define LVT_DELIVERY_MODE_MASK          (0x7 << LVT_DELIVERY_MODE_SHIFT)
#define LVT_DELIVERY_FIXED              (0 << LVT_DELIVERY_MODE_SHIFT)
#define LVT_DELIVERY_NMI                (4 << LVT_DELIVERY_MODE_SHIFT)
#define LVT_DELIVERY_EXTINT             (7 << LVT_DELIVERY_MODE_SHIFT)
#define LVT_POLARITY_ACTIVE_LOW         (1 << 13)
#define LVT_TRIGGER_LEVEL               (1 << 15)
#define LVT_MASK                        (1 << 16)

/* Spurious Interrupt Vector Register bits */
#define SIVR_VECTOR_MASK                0xFF
#define SIVR_APIC_ENABLE                (1 << 8)
#define SIVR_FOCUS_DISABLE              (1 << 9)

/*
 * Check if x2APIC mode is locked and cannot be disabled.
 * Returns true if x2APIC is locked (will #GP on disable attempt).
 */
static bool x2apic_is_locked(void)
{
    uint32_t eax, ebx, ecx, edx;

    /* Check CPUID for IA32_ARCH_CAPABILITIES support (leaf 7, ECX bit 29) */
    asm volatile ("cpuid"
        : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
        : "a"(7), "c"(0));

    if (!(edx & (1 << 29))) {
        /* IA32_ARCH_CAPABILITIES not supported, no lock possible */
        return false;
    }

    /* Check if IA32_XAPIC_DISABLE_STATUS MSR exists */
    uint64_t arch_cap = rdmsr(MSR_IA32_ARCH_CAPABILITIES);
    if (!(arch_cap & ARCH_CAP_XAPIC_DISABLE)) {
        /* MSR not supported, no lock possible */
        return false;
    }

    /* Read the lock status */
    uint64_t xapic_status = rdmsr(MSR_IA32_XAPIC_DISABLE_STATUS);
    return !!(xapic_status & XAPIC_DISABLE_LEGACY_DISABLED);
}

static bool lvt_should_mask(uint32_t lvt)
{
    switch ((lvt >> LVT_DELIVERY_MODE_SHIFT) & 7) {
        case 0b000: /* Fixed */
        case 0b001: /* Lowest Priority */
        case 0b100: /* NMI */
        case 0b111: /* ExtINT */
            return true;
        default:    /* SMI, INIT, Reserved */
            return false;
    }
}

/* MADT NMI routing (loaded once by apic_prepare_for_legacy). */
static uint8_t  g_nmi_lint = 1;       /* default: NMI on LINT1 */
static uint16_t g_nmi_madt_flags = 0; /* MADT polarity/trigger flags */

static void load_nmi_madt_info(void)
{
    struct uacpi_table madt_table;
    if (uacpi_table_find_by_signature(ACPI_MADT_SIGNATURE, &madt_table)
            != UACPI_STATUS_OK) {
        return;
    }
    struct acpi_madt *madt = (struct acpi_madt *)madt_table.virt_addr;
    uint8_t *entry = (uint8_t *)(madt + 1);
    uint8_t *end = (uint8_t *)madt + madt->hdr.length;

    while (entry < end) {
        struct acpi_entry_hdr *hdr = (struct acpi_entry_hdr *)entry;
        if (hdr->length < 2) break;
        if (hdr->type == ACPI_MADT_ENTRY_TYPE_LAPIC_NMI) {
            struct acpi_madt_lapic_nmi *nmi =
                (struct acpi_madt_lapic_nmi *)entry;
            g_nmi_lint = nmi->lint & 1;
            g_nmi_madt_flags = nmi->flags;
            break;
        }
        entry += hdr->length;
    }
    uacpi_table_unref(&madt_table);
}

/* Build the LVT value (delivery mode + polarity/trigger) for one LINT pin.
 * The pin matching MADT's NMI routing gets NMI delivery with MADT-supplied
 * polarity/trigger; the other gets ExtINT (edge, active high). */
static uint32_t lint_lvt_value(int pin)
{
    if (pin == g_nmi_lint) {
        uint32_t val = LVT_DELIVERY_NMI;
        if ((g_nmi_madt_flags & ACPI_MADT_POLARITY_MASK)
                == ACPI_MADT_POLARITY_ACTIVE_LOW)
            val |= LVT_POLARITY_ACTIVE_LOW;
        if ((g_nmi_madt_flags & ACPI_MADT_TRIGGERING_MASK)
                == ACPI_MADT_TRIGGERING_LEVEL)
            val |= LVT_TRIGGER_LEVEL;
        return val;
    }
    return LVT_DELIVERY_EXTINT;
}

/*
 * Configure LAPIC for legacy BIOS operation in x2APIC mode (MSR access).
 * Sets up LINT0/LINT1 per MADT-reported NMI routing (default: LINT1=NMI).
 *
 * Note: The LAPIC ignores trigger mode for ExtINT and NMI delivery modes,
 * always using edge-triggered internally.
 */
static void x2apic_configure_for_legacy(void)
{
    uint64_t val;
    uint32_t max_lvt = ((uint32_t)rdmsr(X2APIC_MSR_VERSION) >> 16) & 0xFF;

    /* Clear task priority to allow all interrupts */
    wrmsr(X2APIC_MSR_TPR, 0);

    /* Mask stale LVT entries to prevent unexpected interrupts.
     * Only mask entries with Fixed, Lowest Priority, NMI, or ExtINT delivery
     * mode. Leave SMI, INIT, and reserved delivery modes untouched as firmware
     * may rely on them (e.g. thermal management via SMI). */
    uint64_t lvt;
    lvt = rdmsr(X2APIC_MSR_LVT_TIMER);
    if (lvt_should_mask(lvt))
        wrmsr(X2APIC_MSR_LVT_TIMER, lvt | LVT_MASK);
    lvt = rdmsr(X2APIC_MSR_LVT_ERROR);
    if (lvt_should_mask(lvt))
        wrmsr(X2APIC_MSR_LVT_ERROR, lvt | LVT_MASK);
    if (max_lvt >= 4) {
        lvt = rdmsr(X2APIC_MSR_LVT_PMC);
        if (lvt_should_mask(lvt))
            wrmsr(X2APIC_MSR_LVT_PMC, lvt | LVT_MASK);
    }
    if (max_lvt >= 5) {
        lvt = rdmsr(X2APIC_MSR_LVT_THERMAL);
        if (lvt_should_mask(lvt))
            wrmsr(X2APIC_MSR_LVT_THERMAL, lvt | LVT_MASK);
    }
    if (max_lvt >= 6) {
        lvt = rdmsr(X2APIC_MSR_LVT_CMCI);
        if (lvt_should_mask(lvt))
            wrmsr(X2APIC_MSR_LVT_CMCI, lvt | LVT_MASK);
    }

    /* Configure LINT0 / LINT1: one gets NMI (per MADT), the other ExtINT. */
    val = rdmsr(X2APIC_MSR_LVT_LINT0);
    printf("  x2APIC LINT0 before: 0x%08lx\n", (uint32_t)val);
    val &= ~(LVT_VECTOR_MASK | LVT_DELIVERY_MODE_MASK | LVT_TRIGGER_LEVEL |
             LVT_POLARITY_ACTIVE_LOW | LVT_MASK);
    val |= lint_lvt_value(0);
    wrmsr(X2APIC_MSR_LVT_LINT0, val);
    printf("  x2APIC LINT0 after:  0x%08lx\n", (uint32_t)rdmsr(X2APIC_MSR_LVT_LINT0));

    val = rdmsr(X2APIC_MSR_LVT_LINT1);
    printf("  x2APIC LINT1 before: 0x%08lx\n", (uint32_t)val);
    val &= ~(LVT_VECTOR_MASK | LVT_DELIVERY_MODE_MASK | LVT_TRIGGER_LEVEL |
             LVT_POLARITY_ACTIVE_LOW | LVT_MASK);
    val |= lint_lvt_value(1);
    wrmsr(X2APIC_MSR_LVT_LINT1, val);
    printf("  x2APIC LINT1 after:  0x%08lx\n", (uint32_t)rdmsr(X2APIC_MSR_LVT_LINT1));

    /* Configure Spurious Interrupt Vector Register:
     * - APIC software enable (bit 8) - required for LAPIC to work
     * - Spurious vector = 0x0F (matches legacy 8259 PIC IRQ7 spurious interrupt)
     */
    val = rdmsr(X2APIC_MSR_SIVR);
    printf("  x2APIC SIVR before:  0x%08lx\n", (uint32_t)val);
    val &= ~SIVR_VECTOR_MASK;
    val |= SIVR_APIC_ENABLE | 0x0F;
    wrmsr(X2APIC_MSR_SIVR, val);
    printf("  x2APIC SIVR after:   0x%08lx\n", (uint32_t)rdmsr(X2APIC_MSR_SIVR));
}

/*
 * Configure LAPIC for legacy BIOS operation in xAPIC mode (MMIO access).
 * Sets up LINT0 for ExtINT, LINT1 for NMI per Intel SDM Appendix D.
 *
 * Note: The LAPIC ignores trigger mode for ExtINT and NMI delivery modes,
 * always using edge-triggered internally. We set edge-triggered explicitly
 * to match Intel's documented example (0x0700 for ExtINT, 0x0400 for NMI).
 */
static void xapic_configure_for_legacy(uintptr_t apic_base)
{
    volatile uint32_t *lint0_reg = (volatile uint32_t *)(apic_base + XAPIC_LVT_LINT0_OFFSET);
    volatile uint32_t *lint1_reg = (volatile uint32_t *)(apic_base + XAPIC_LVT_LINT1_OFFSET);
    volatile uint32_t *sivr_reg = (volatile uint32_t *)(apic_base + XAPIC_SIVR_OFFSET);
    uint32_t val;
    uint32_t max_lvt = (*(volatile uint32_t *)(apic_base + XAPIC_VERSION_OFFSET) >> 16) & 0xFF;

    /* Clear task priority to allow all interrupts */
    *(volatile uint32_t *)(apic_base + XAPIC_TPR_OFFSET) = 0;

    /* Mask stale LVT entries to prevent unexpected interrupts.
     * Only mask entries with Fixed, Lowest Priority, NMI, or ExtINT delivery
     * mode. Leave SMI, INIT, and reserved delivery modes untouched as firmware
     * may rely on them (e.g. thermal management via SMI). */
    uint32_t lvt;
    lvt = *(volatile uint32_t *)(apic_base + XAPIC_LVT_TIMER_OFFSET);
    if (lvt_should_mask(lvt))
        *(volatile uint32_t *)(apic_base + XAPIC_LVT_TIMER_OFFSET) = lvt | LVT_MASK;
    lvt = *(volatile uint32_t *)(apic_base + XAPIC_LVT_ERROR_OFFSET);
    if (lvt_should_mask(lvt))
        *(volatile uint32_t *)(apic_base + XAPIC_LVT_ERROR_OFFSET) = lvt | LVT_MASK;
    if (max_lvt >= 4) {
        lvt = *(volatile uint32_t *)(apic_base + XAPIC_LVT_PMC_OFFSET);
        if (lvt_should_mask(lvt))
            *(volatile uint32_t *)(apic_base + XAPIC_LVT_PMC_OFFSET) = lvt | LVT_MASK;
    }
    if (max_lvt >= 5) {
        lvt = *(volatile uint32_t *)(apic_base + XAPIC_LVT_THERMAL_OFFSET);
        if (lvt_should_mask(lvt))
            *(volatile uint32_t *)(apic_base + XAPIC_LVT_THERMAL_OFFSET) = lvt | LVT_MASK;
    }
    if (max_lvt >= 6) {
        lvt = *(volatile uint32_t *)(apic_base + XAPIC_LVT_CMCI_OFFSET);
        if (lvt_should_mask(lvt))
            *(volatile uint32_t *)(apic_base + XAPIC_LVT_CMCI_OFFSET) = lvt | LVT_MASK;
    }

    /* Configure LINT0 / LINT1: one gets NMI (per MADT), the other ExtINT. */
    val = *lint0_reg;
    printf("  xAPIC LINT0 before: 0x%08x\n", val);
    val &= ~(LVT_VECTOR_MASK | LVT_DELIVERY_MODE_MASK | LVT_TRIGGER_LEVEL |
             LVT_POLARITY_ACTIVE_LOW | LVT_MASK);
    val |= lint_lvt_value(0);
    *lint0_reg = val;
    printf("  xAPIC LINT0 after:  0x%08x\n", *lint0_reg);

    val = *lint1_reg;
    printf("  xAPIC LINT1 before: 0x%08x\n", val);
    val &= ~(LVT_VECTOR_MASK | LVT_DELIVERY_MODE_MASK | LVT_TRIGGER_LEVEL |
             LVT_POLARITY_ACTIVE_LOW | LVT_MASK);
    val |= lint_lvt_value(1);
    *lint1_reg = val;
    printf("  xAPIC LINT1 after:  0x%08x\n", *lint1_reg);

    /* Configure Spurious Interrupt Vector Register:
     * - APIC software enable (bit 8) - required for LAPIC to work
     * - Spurious vector = 0x0F (matches legacy 8259 PIC IRQ7 spurious interrupt)
     */
    val = *sivr_reg;
    printf("  xAPIC SIVR before:  0x%08x\n", val);
    val &= ~SIVR_VECTOR_MASK;
    val |= SIVR_APIC_ENABLE | 0x0F;
    *sivr_reg = val;
    printf("  xAPIC SIVR after:   0x%08x\n", *sivr_reg);
}

/*
 * Prepare APIC for legacy BIOS operation.
 *
 * This function handles the APIC configuration needed for legacy software
 * that expects PIC interrupts (especially IRQ0 timer) to work correctly.
 *
 * Strategy: Keep LAPIC enabled in xAPIC mode with LINT0 configured for
 * ExtINT passthrough. This matches QEMU's default behavior and is the
 * standard configuration for legacy BIOS systems.
 *
 * - If in x2APIC mode (not locked): transition to xAPIC, configure ExtINT
 * - If in x2APIC mode (locked): configure ExtINT via MSR (cannot leave x2APIC)
 * - If already in xAPIC mode: configure ExtINT via MMIO
 */
void apic_prepare_for_legacy(void)
{
    uint64_t apic_base_msr;
    uintptr_t apic_base_addr;
    bool lapic_enabled, x2apic_enabled;

    printf("Configuring APIC for legacy BIOS compatibility...\n");

    load_nmi_madt_info();
    printf("  NMI on LINT%u (MADT flags 0x%04x)\n", g_nmi_lint, g_nmi_madt_flags);

    /* Read current APIC state */
    apic_base_msr = rdmsr(MSR_IA32_APIC_BASE);
    apic_base_addr = apic_base_msr & APIC_BASE_ADDR_MASK;
    lapic_enabled = !!(apic_base_msr & APIC_BASE_EN);
    x2apic_enabled = !!(apic_base_msr & APIC_BASE_EXTD);

    printf("  IA32_APIC_BASE: 0x%016lx (addr=0x%lx, EN=%d, x2APIC=%d, BSP=%d)\n",
           apic_base_msr, apic_base_addr,
           lapic_enabled, x2apic_enabled,
           !!(apic_base_msr & APIC_BASE_BSP));

    if (!lapic_enabled) {
        printf("  LAPIC disabled, enabling in xAPIC mode\n");
        apic_base_msr |= APIC_BASE_EN;
        apic_base_msr &= ~APIC_BASE_EXTD;
        wrmsr(MSR_IA32_APIC_BASE, apic_base_msr);
        apic_base_addr = apic_base_msr & APIC_BASE_ADDR_MASK;
        xapic_configure_for_legacy(apic_base_addr);
        printf("  APIC configuration complete\n");
        return;
    }

    if (x2apic_enabled) {
        /* Check if x2APIC mode is locked */
        bool locked = x2apic_is_locked();
        printf("  x2APIC lock status: %s\n", locked ? "LOCKED" : "not locked");

        if (!locked) {
            /*
             * Transition from x2APIC to xAPIC mode.
             * Cannot go directly x2APIC -> xAPIC (causes #GP).
             * Must disable first, then re-enable in xAPIC mode.
             */
            printf("  Transitioning x2APIC -> xAPIC mode\n");

            /* Step 1: Disable LAPIC (clear both EN and EXTD) */
            apic_base_msr &= ~(APIC_BASE_EN | APIC_BASE_EXTD);
            wrmsr(MSR_IA32_APIC_BASE, apic_base_msr);

            /* Step 2: Re-enable in xAPIC mode (set EN, keep EXTD clear) */
            apic_base_msr |= APIC_BASE_EN;
            wrmsr(MSR_IA32_APIC_BASE, apic_base_msr);

            /* Verify transition */
            apic_base_msr = rdmsr(MSR_IA32_APIC_BASE);
            printf("  IA32_APIC_BASE after: 0x%016lx (EN=%d, x2APIC=%d)\n",
                   apic_base_msr,
                   !!(apic_base_msr & APIC_BASE_EN),
                   !!(apic_base_msr & APIC_BASE_EXTD));

            /* Now configure LAPIC via MMIO */
            xapic_configure_for_legacy(apic_base_addr);
        } else {
            /*
             * x2APIC is locked. Cannot leave x2APIC mode without #GP.
             * Configure LAPIC for legacy operation via MSR.
             */
            printf("  x2APIC locked, configuring for legacy via MSR\n");
            x2apic_configure_for_legacy();
        }
    } else {
        /*
         * Already in xAPIC mode. Configure LAPIC via MMIO.
         * This matches QEMU's default LAPIC configuration.
         */
        printf("  Configuring xAPIC for legacy operation\n");
        xapic_configure_for_legacy(apic_base_addr);
    }

    printf("  APIC configuration complete\n");
}
