obj-$(CONFIG_EFI) 		+= efi.o efi_$(BITS).o

ifdef CONFIG_CC_LTO
lib-$(CONFIG_EFI) 		+= efi_stub_$(BITS).o
else
obj-$(CONFIG_EFI) 		+= efi_stub_$(BITS).o
endif
