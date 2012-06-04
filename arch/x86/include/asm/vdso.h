#ifndef _ASM_X86_VDSO_H
#define _ASM_X86_VDSO_H

#if defined CONFIG_X86_32 || defined CONFIG_COMPAT
#ifdef CONFIG_CC_LTO
#define VDSO32_PRELINK			0
#define VDSO32_SYSENTER_RETURN		0x0430
#define VDSO32_rt_sigreturn		0x0410
#define VDSO32_sigreturn		0x0400
#define VDSO32_vsyscall			0x0420
#define VDSO32_vsyscall_eh_frame_size	0x040
#define VDSO32_SYMBOL(base, name)	((void __user *)(VDSO32_##name - VDSO32_PRELINK + (unsigned long)(base)))
#else
extern const char VDSO32_PRELINK[];

/*
 * Given a pointer to the vDSO image, find the pointer to VDSO32_name
 * as that symbol is defined in the vDSO sources or linker script.
 */
#define VDSO32_SYMBOL(base, name)					\
({									\
	extern const char VDSO32_##name[];				\
	(void __user *)(VDSO32_##name - VDSO32_PRELINK + (unsigned long)(base)); \
})
#endif
#endif

/*
 * These symbols are defined with the addresses in the vsyscall page.
 * See vsyscall-sigreturn.S.
 */
extern void __user __kernel_sigreturn;
extern void __user __kernel_rt_sigreturn;

/*
 * These symbols are defined by vdso32.S to mark the bounds
 * of the ELF DSO images included therein.
 */
extern const char vdso32_int80_start, vdso32_int80_end;
extern const char vdso32_syscall_start, vdso32_syscall_end;
extern const char vdso32_sysenter_start, vdso32_sysenter_end;

#endif /* _ASM_X86_VDSO_H */
