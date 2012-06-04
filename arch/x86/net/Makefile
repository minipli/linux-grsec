#
# Arch-specific network modules
#
obj-$(CONFIG_BPF_JIT) += bpf_jit_comp.o
ifdef CONFIG_CC_LTO
lib-$(CONFIG_BPF_JIT) := bpf_jit.o
else
obj-$(CONFIG_BPF_JIT) += bpf_jit.o
endif
