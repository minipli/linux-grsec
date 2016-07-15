GCC_PLUGINS_DIR := $(shell $(CC) -print-file-name=plugin)

ifeq ($(PLUGINCC),$(HOSTCC))
  HOSTLIBS := hostlibs
  HOST_EXTRACFLAGS += -I$(GCC_PLUGINS_DIR)/include -I$(src) -std=gnu99 -ggdb -Wall -W
  export HOST_EXTRACFLAGS
else
  HOSTLIBS := hostcxxlibs
  HOST_EXTRACXXFLAGS += -I$(GCC_PLUGINS_DIR)/include -I$(src) -std=gnu++98 -fno-rtti
  HOST_EXTRACXXFLAGS += -fno-exceptions -fasynchronous-unwind-tables -ggdb
  HOST_EXTRACXXFLAGS += -Wno-narrowing -Wno-unused-variable
  HOST_EXTRACXXFLAGS += -Wall -W -Wno-unused-parameter
  export HOST_EXTRACXXFLAGS
endif

export HOSTLIBS

$(HOSTLIBS)-y := $(foreach p,$(GCC_PLUGIN),$(if $(findstring /,$(p)),,$(p)))
always := $($(HOSTLIBS)-y)
$(foreach p,$($(HOSTLIBS)-y:%.so=%),$(eval $(p)-objs := $(p).o))

subdir-y := $(GCC_PLUGIN_SUBDIR)
subdir-  += $(GCC_PLUGIN_SUBDIR)

clean-files += *.so
