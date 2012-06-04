/*
 * Copyright 2011 by the PaX Team <pageexec@freemail.hu>
 * Licensed under the GPL v2
 *
 * Note: the choice of the license means that the compilation process is
 *       NOT 'eligible' as defined by gcc's library exception to the GPL v3,
 *       but for the kernel it doesn't matter since it doesn't link against
 *       any of the gcc libraries
 *
 * gcc plugin to allow -flto to link vmlinux
 *
 * TODO:
 *
 * BUGS:
 * - none known
 */
#include "gcc-plugin.h"
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tree.h"
#include "tree-pass.h"
#include "intl.h"
#include "plugin-version.h"
#include "tm.h"
#include "toplev.h"
#include "basic-block.h"
#include "gimple.h"
//#include "expr.h" where are you...
#include "diagnostic.h"
#include "rtl.h"
#include "emit-rtl.h"
#include "function.h"
#include "tree-flow.h"
#include "target.h"
#include "plugin.h"
#include "output.h"

extern void print_gimple_stmt(FILE *, gimple, int, int);
extern rtx emit_move_insn(rtx x, rtx y);

int plugin_is_GPL_compatible;

static struct plugin_info checker_plugin_info = {
	.version	= "201110031940",
};

static unsigned int execute_lto_tree(void);
static unsigned int execute_lto_final(void);

static struct gimple_opt_pass lto_tree_pass = {
	.pass = {
		.type			= GIMPLE_PASS,
		.name			= "lto_tree",
		.gate			= NULL,
		.execute		= execute_lto_tree,
		.sub			= NULL,
		.next			= NULL,
		.static_pass_number	= 0,
		.tv_id			= TV_NONE,
		.properties_required	= PROP_gimple_leh | PROP_cfg,
		.properties_provided	= 0,
		.properties_destroyed	= 0,
		.todo_flags_start	= 0, //TODO_verify_ssa | TODO_verify_flow | TODO_verify_stmts,
		.todo_flags_finish	= TODO_verify_stmts | TODO_dump_func
	}
};

static struct rtl_opt_pass lto_rtl_opt_pass = {
	.pass = {
		.type			= RTL_PASS,
		.name			= "lto_final",
		.gate			= NULL,
		.execute		= execute_lto_final,
		.sub			= NULL,
		.next			= NULL,
		.static_pass_number	= 0,
		.tv_id			= TV_NONE,
		.properties_required	= 0,
		.properties_provided	= 0,
		.properties_destroyed	= 0,
		.todo_flags_start	= 0,
		.todo_flags_finish	= TODO_dump_func
	}
};

/*
!DECL_HAS_VALUE_EXPR_P (exp) ?
if (!DECL_EXTERNAL (exp) && TREE_CODE (exp) == VAR_DECL && DECL_SECTION_NAME (exp) && IN_NAMED_SECTION (exp))
	const char *section = TREE_STRING_POINTER (DECL_SECTION_NAME (exp));
	strcmp(section, ".rodata");
*/

static void finish_type(void *event_data, void *data)
{
	tree type = (tree)event_data;

	if (type == NULL_TREE)
		return;

//	if (TYPE_READONLY(type))
//		debug_tree(type);
}

static unsigned int execute_lto_tree(void)
{
	basic_block bb, entry_bb;
	gimple_stmt_iterator gsi;

//	entry_bb = ENTRY_BLOCK_PTR_FOR_FUNCTION(cfun)->next_bb;

	FOR_EACH_BB(bb) {
		for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
//			tree decl;
			gimple stmt = gsi_stmt(gsi);

			if (!is_gimple_call(stmt))
				continue;
		}
	}

	return 0;
}

static unsigned int execute_lto_final(void)
{
	return 0;
}


static struct {
	const char *name;
	const char *asm_op;
} sections[] = {
	{".init.rodata",    "\t.section\t.init.rodata,\"a\""},
	{".ref.rodata",     "\t.section\t.ref.rodata,\"a\""},
	{".devinit.rodata", "\t.section\t.devinit.rodata,\"a\""},
	{".devexit.rodata", "\t.section\t.devexit.rodata,\"a\""},
	{".cpuinit.rodata", "\t.section\t.cpuinit.rodata,\"a\""},
	{".cpuexit.rodata", "\t.section\t.cpuexit.rodata,\"a\""},
	{".meminit.rodata", "\t.section\t.meminit.rodata,\"a\""},
	{".memexit.rodata", "\t.section\t.memexit.rodata,\"a\""},
};

static unsigned int (*old_section_type_flags)(tree decl, const char *name, int reloc);

static unsigned int lto_section_type_flags(tree decl, const char *name, int reloc)
{
	size_t i;

	for (i = 0; i < ARRAY_SIZE(sections); i++)
		if (!strcmp(sections[i].name, name))
			return 0;
	return old_section_type_flags(decl, name, reloc);
}

static void lto_start_unit(void *gcc_data, void *user_data)
{
//	size_t i;

//	for (i = 0; i < ARRAY_SIZE(sections); i++)
//		sections[i].section = get_unnamed_section(0, output_section_asm_op, sections[i].asm_op);
//		sections[i].section = get_section(sections[i].name, 0, NULL);

	old_section_type_flags = targetm.section_type_flags;
	targetm.section_type_flags = lto_section_type_flags;
}

int plugin_init(struct plugin_name_args *plugin_info, struct plugin_gcc_version *version)
{
	const char * const plugin_name = plugin_info->base_name;
	const int argc = plugin_info->argc;
	const struct plugin_argument * const argv = plugin_info->argv;
	int i;
#if 0
	struct register_pass_info lto_tree_pass_info = {
		.pass				= &lto_tree_pass.pass,
		.reference_pass_name		= "optimized",
		.ref_pass_instance_number	= 0,
		.pos_op 			= PASS_POS_INSERT_AFTER
	};
	struct register_pass_info lto_rtl_pass_info = {
		.pass				= &lto_rtl_opt_pass.pass,
		.reference_pass_name		= "final",
		.ref_pass_instance_number	= 0,
		.pos_op 			= PASS_POS_INSERT_BEFORE
	};
#endif

	if (!plugin_default_version_check(version, &gcc_version)) {
		error(G_("incompatible gcc/plugin versions"));
		return 1;
	}

	register_callback(plugin_name, PLUGIN_INFO, NULL, &checker_plugin_info);

	for (i = 0; i < argc; ++i)
		error(G_("unkown option '-fplugin-arg-%s-%s'"), plugin_name, argv[i].key);

	if (TARGET_64BIT == 0)
		return 0;

//	register_callback(plugin_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &lto_tree_pass_info);
//	register_callback(plugin_name, PLUGIN_PASS_MANAGER_SETUP, NULL, &lto_rtl_pass_info);

//	register_callback(plugin_name, PLUGIN_FINISH_TYPE, finish_type, NULL);

	register_callback(plugin_name, PLUGIN_START_UNIT, lto_start_unit, NULL);
	return 0;
}
