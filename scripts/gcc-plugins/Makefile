GCC_PLUGINS_DIR := $(shell $(CC) -print-file-name=plugin)

ifeq ($(PLUGINCC),$(HOSTCC))
  HOSTLIBS := hostlibs
  HOST_EXTRACFLAGS += -I$(GCC_PLUGINS_DIR)/include -I$(src)
  HOST_EXTRACFLAGS += -std=gnu99 -ggdb -fvisibility=hidden
  HOST_EXTRACFLAGS += -Wall -W
  export HOST_EXTRACFLAGS
else
  HOSTLIBS := hostcxxlibs
  HOST_EXTRACXXFLAGS += -I$(GCC_PLUGINS_DIR)/include -I$(src)
  HOST_EXTRACXXFLAGS += -std=gnu++98 -ggdb -fvisibility=hidden
  HOST_EXTRACXXFLAGS += -fno-rtti -fno-exceptions -fasynchronous-unwind-tables
  HOST_EXTRACXXFLAGS += -Wall -W
  HOST_EXTRACXXFLAGS += -Wno-unused-parameter -Wno-narrowing -Wno-unused-variable
  export HOST_EXTRACXXFLAGS
endif

ifneq ($(CFLAGS_KCOV), $(SANCOV_PLUGIN))
  GCC_PLUGIN := $(filter-out $(SANCOV_PLUGIN), $(GCC_PLUGIN))
endif

export HOSTLIBS

$(HOSTLIBS)-y := $(foreach p,$(GCC_PLUGIN),$(if $(findstring /,$(p)),,$(p)))
always := $($(HOSTLIBS)-y)
$(foreach p,$($(HOSTLIBS)-y:%.so=%),$(eval $(p)-objs := $(p).o))

subdir-y := $(GCC_PLUGIN_SUBDIR)
subdir-  += $(GCC_PLUGIN_SUBDIR)

clean-files += *.so
