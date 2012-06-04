# __restore_processor_state() restores %gs after S3 resume and so should not
# itself be stack-protected
nostackp := $(call cc-option, -fno-stack-protector)
CFLAGS_cpu.o	:= $(nostackp)

obj-$(CONFIG_PM_SLEEP)		+= cpu.o
obj-$(CONFIG_HIBERNATION)	+= hibernate_$(BITS).o
ifdef CONFIG_CC_LTO
lib-$(CONFIG_HIBERNATION)	:= hibernate_asm_$(BITS).o
else
obj-$(CONFIG_HIBERNATION)	+= hibernate_asm_$(BITS).o
endif
