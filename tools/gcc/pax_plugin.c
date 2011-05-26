/*
 * Copyright 2011 by the PaX Team <pageexec@freemail.hu>
 * Licensed under the GPL v2
 *
 * Note: the choice of the license means that the compilation process is
 *       NOT 'eligible' as defined by gcc's library exception to the GPL v3,
 *       but for the kernel it doesn't matter since it doesn't link against
 *       any of the gcc libraries
 *
 * gcc plugin to help implement various PaX features
 *
 * - track lowest stack pointer
 *
 * TODO:
 * - initialize all local variables
 *
 * BUGS:
 * - -mpreferred-stack-boundary=2 is needed else gcc asserts
 */
#include "gcc-plugin.h"
#include "plugin-version.h"
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "toplev.h"
//#include "basic-block.h"
//#include "gimple.h"
//#include "expr.h" where are you...
#include "rtl.h"
#include "function.h"
#include "tree.h"
#include "tree-pass.h"
#include "intl.h"

const int plugin_is_GPL_compatible;

static int track_frame_size = -1;
static const char track_function[] = "pax_track_stack";
static bool init_locals;

static struct plugin_info pax_plugin_info = {
	.version	= "201105261520",
	.help		= "track-lowest-sp=nn\ttrack sp in functions whose frame size is at least nn bytes\n"
//			  "initialize-locals\t\tforcibly initialize all stack frames\n"
};

static unsigned int pax_handle_expand(void);
static struct rtl_opt_pass pax_expand_rtl_opt_pass = {
	.pass = {
		.type			= RTL_PASS,
		.name			= "pax_expand",
		.gate			= NULL,
		.execute		= pax_handle_expand,
		.sub			= NULL,
		.next			= NULL,
		.static_pass_number	= 0,
		.tv_id			= TV_NONE,
		.properties_required	= 0,
		.properties_provided	= 0,
		.properties_destroyed	= 0,
		.todo_flags_start	= 0,
		.todo_flags_finish	= 0
	}
};

rtx init_one_libfunc(const char *name);
tree build_libfunc_function(const char *name);

static unsigned int pax_handle_expand(void)
{
	rtx track, insn;

	if (track_frame_size < 0)
		return 0;

	// 0. already instrumented?
	for (insn = get_insns(); insn; insn = NEXT_INSN(insn)) {
		// rtl match: (call_insn 8 7 9 3 a.c:9 (call (mem (symbol_ref ("pax_track_stack") [flags 0x41] <function_decl 0xb7470e80 pax_track_stack>) [0 S1 A8]) (4)) -1 (nil) (nil))
		rtx body;

		if (!CALL_P(insn))
			continue;
		body = PATTERN(insn);
		if (GET_CODE(body) != CALL)
			continue;
		body = XEXP(body, 0);
		if (GET_CODE(body) != MEM)
			continue;
		body = XEXP(body, 0);
		if (GET_CODE(body) != SYMBOL_REF)
			continue;
		if (!strcmp(XSTR(body, 0), track_function))
			return 0;
	}

	// 1. if function has a variable frame length
	if (cfun->calls_alloca) {
		// 1.1 for each stack adjustment insn
		for (insn = get_insns(); insn; insn = NEXT_INSN(insn)) {
			// rtl match: (insn 11 10 12 3 a.c:12 (parallel [ (set (reg 7 sp) (minus (reg 7 sp) (reg 80))) (clobber (reg 17 flags)) ]) -1 (nil))
			rtx body;

			if ((!NONJUMP_INSN_P(insn)))
				continue;
			body = PATTERN(insn);
			if (GET_CODE(body) != PARALLEL)
				continue;
			if (XVECLEN (body, 0) != 2)
				continue;
			body = XVECEXP(body, 0, 0);
			if (GET_CODE(body) != SET)
				continue;
			body = SET_DEST(body);
			if (!REG_P(body))
				continue;
			if (body != stack_pointer_rtx)
				continue;

			// 1.2 insert call to pax_track_stack after
			start_sequence();
			emit_library_call(gen_rtx_SYMBOL_REF(Pmode, track_function), LCT_NORMAL, VOIDmode, 1, stack_pointer_rtx, Pmode);
			track = get_insns();
			end_sequence();
			emit_insn_after(track, insn);
		}
	} else {
		if (get_frame_size() < track_frame_size)
			return 0;
		// 2.1 find first insn
		for (insn = get_insns(); insn; insn = NEXT_INSN(insn))
			if (NOTE_P(insn) && NOTE_KIND(insn) == NOTE_INSN_FUNCTION_BEG)
				break;
		for (; insn; insn = NEXT_INSN(insn))
			if (INSN_P(insn))
				break;

		// 2.2 insert call to pax_track_stack before
		start_sequence();
		emit_library_call(gen_rtx_SYMBOL_REF(Pmode, track_function), LCT_NORMAL, VOIDmode, 1, stack_pointer_rtx, Pmode);
		track = get_insns();
		end_sequence();
		emit_insn_before(track, insn);
	}

//	printf("%u %u %u\n", crtl->stack_alignment_needed, crtl->preferred_stack_boundary, cfun->calls_alloca);
//	print_simple_rtl(stderr, get_insns());
//	print_rtl(stderr, get_insns());
//	warning(0, "track_frame_size: %ld %x", get_frame_size(), track_frame_size);

	return 0;
}

int plugin_init(struct plugin_name_args *plugin_info, struct plugin_gcc_version *version)
{
	const char * const plugin_name = plugin_info->base_name;
	const int argc = plugin_info->argc;
	const struct plugin_argument * const argv = plugin_info->argv;
	int i;
	struct register_pass_info pax_expand_pass_info = {
		.pass				= &pax_expand_rtl_opt_pass.pass,
		.reference_pass_name		= "expand",
		.ref_pass_instance_number	= 0,
		.pos_op 			= PASS_POS_INSERT_AFTER
	};

	if (!plugin_default_version_check(version, &gcc_version)) {
		error(G_("incompatible gcc/plugin versions"));
		return 1;
	}

	register_callback(plugin_name, PLUGIN_INFO, NULL, &pax_plugin_info);

	for (i = 0; i < argc; ++i) {
		if (!strcmp(argv[i].key, "track-lowest-sp")) {
			if (!argv[i].value) {
				error(G_("no value supplied for option '-fplugin-arg-%s-%s'"), plugin_name, argv[i].key);
				continue;
			}
			track_frame_size = atoi(argv[i].value);
			if (argv[i].value[0] < '0' || argv[i].value[0] > '9' || track_frame_size < 0)
				error(G_("invalid option argument '-fplugin-arg-%s-%s=%s'"), plugin_name, argv[i].key, argv[i].value);
			continue;
		}
		if (!strcmp(argv[i].key, "initialize-locals")) {
			if (argv[i].value) {
				error(G_("invalid option argument '-fplugin-arg-%s-%s=%s'"), plugin_name, argv[i].key, argv[i].value);
				continue;
			}
			init_locals = true;
			continue;
		}
		error(G_("unkown option '-fplugin-arg-%s-%s'"), plugin_name, argv[i].key);
	}

	register_callback(plugin_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &pax_expand_pass_info);
	return 0;
}
