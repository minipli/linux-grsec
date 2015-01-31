/*
 * Copyright 2011-2015 by Emese Revfy <re.emese@gmail.com>
 * Licensed under the GPL v2, or (at your option) v3
 *
 * Homepage:
 * http://www.grsecurity.net/~ephox/overflow_plugin/
 *
 * Documentation:
 * http://forums.grsecurity.net/viewtopic.php?f=7&t=3043
 *
 * This plugin recomputes expressions of function arguments marked by a size_overflow attribute
 * with double integer precision (DImode/TImode for 32/64 bit integer types).
 * The recomputed argument is checked against TYPE_MAX and an event is logged on overflow and the triggering process is killed.
 *
 * Usage:
 * $ make
 * $ make run
 */

#include "size_overflow.h"

static tree cast_to_orig_type(struct visited *visited, gimple stmt, const_tree orig_node, tree new_node)
{
	const_gimple assign;
	tree orig_type = TREE_TYPE(orig_node);
	gimple_stmt_iterator gsi = gsi_for_stmt(stmt);

	assign = build_cast_stmt(visited, orig_type, new_node, CREATE_NEW_VAR, &gsi, BEFORE_STMT, false);
	return gimple_assign_lhs(assign);
}

static void change_size_overflow_asm_input(gimple stmt, tree new_input)
{
	tree list;

	gcc_assert(is_size_overflow_insert_check_asm(stmt));

	list = build_tree_list(NULL_TREE, build_string(3, "rm"));
	list = chainon(NULL_TREE, build_tree_list(list, new_input));
	gimple_asm_set_input_op(stmt, 0, list);
}

static void change_orig_node(struct visited *visited, gimple stmt, const_tree orig_node, tree new_node, unsigned int num)
{
	tree cast_lhs = cast_to_orig_type(visited, stmt, orig_node, new_node);

	switch (gimple_code(stmt)) {
	case GIMPLE_RETURN:
		gimple_return_set_retval(stmt, cast_lhs);
		break;
	case GIMPLE_CALL:
		gimple_call_set_arg(stmt, num - 1, cast_lhs);
		break;
	case GIMPLE_ASM:
		change_size_overflow_asm_input(stmt, cast_lhs);
		break;
	default:
		debug_gimple_stmt(stmt);
		gcc_unreachable();
	}

	update_stmt(stmt);
}

static void set_conditions(struct pointer_set_t *visited, bool *interesting_conditions, const_tree lhs);

static void walk_phi_set_conditions(struct pointer_set_t *visited, bool *interesting_conditions, const_tree result)
{
	gimple phi = get_def_stmt(result);
	unsigned int i, n = gimple_phi_num_args(phi);

	pointer_set_insert(visited, phi);
	for (i = 0; i < n; i++) {
		const_tree arg = gimple_phi_arg_def(phi, i);

		set_conditions(visited, interesting_conditions, arg);
	}
}

enum conditions {
	NOT_UNARY, CAST
};

// Search for constants, cast assignments and binary/ternary assignments
static void set_conditions(struct pointer_set_t *visited, bool *interesting_conditions, const_tree lhs)
{
	gimple def_stmt = get_def_stmt(lhs);

	if (!def_stmt)
		return;

	if (pointer_set_contains(visited, def_stmt))
		return;

	switch (gimple_code(def_stmt)) {
	case GIMPLE_CALL:
	case GIMPLE_NOP:
	case GIMPLE_ASM:
		if (is_size_overflow_asm(def_stmt))
			set_conditions(visited, interesting_conditions, get_size_overflow_asm_input(def_stmt));
		return;
	case GIMPLE_PHI:
		return walk_phi_set_conditions(visited, interesting_conditions, lhs);
	case GIMPLE_ASSIGN:
		if (gimple_num_ops(def_stmt) == 2) {
			const_tree rhs = gimple_assign_rhs1(def_stmt);

			if (gimple_assign_cast_p(def_stmt))
				interesting_conditions[CAST] = true;

			return set_conditions(visited, interesting_conditions, rhs);
		} else {
			interesting_conditions[NOT_UNARY] = true;
			return;
		}
	default:
		debug_gimple_stmt(def_stmt);
		gcc_unreachable();
	}
}

static void search_interesting_conditions(const_tree node, bool *interesting_conditions)
{
	struct pointer_set_t *visited;

	visited = pointer_set_create();
	set_conditions(visited, interesting_conditions, node);
	pointer_set_destroy(visited);
}

// e.g., 3.8.2, 64, arch/x86/ia32/ia32_signal.c copy_siginfo_from_user32(): compat_ptr() u32 max
static bool skip_asm_cast(const_tree arg)
{
	gimple def_stmt = get_def_stmt(arg);

	if (!def_stmt || !gimple_assign_cast_p(def_stmt))
		return false;

	def_stmt = get_def_stmt(gimple_assign_rhs1(def_stmt));
	if (is_size_overflow_asm(def_stmt))
		return false;
	return def_stmt && gimple_code(def_stmt) == GIMPLE_ASM;
}

/* If there is a mark_turn_off intentional attribute on the caller or the callee then there is no duplication and missing size_overflow attribute check anywhere.
 * There is only missing size_overflow attribute checking if the intentional_overflow attribute is the mark_no type.
 * Stmt duplication is unnecessary if there are no binary/ternary assignements or if the unary assignment isn't a cast.
 */
static bool skip_unnecessary_insertation(const_tree node)
{
	bool interesting_conditions[2] = {false, false};

	search_interesting_conditions(node, interesting_conditions);

	// unnecessary overflow check
	return !interesting_conditions[CAST] && !interesting_conditions[NOT_UNARY];
}

struct interesting_stmts {
	struct interesting_stmts *next;
	gimple first_stmt;
	tree orig_node;
	unsigned int num;
};

static struct interesting_stmts *create_interesting_stmts(struct interesting_stmts *head, tree orig_node, gimple first_stmt, unsigned int num)
{
	struct interesting_stmts *new_node;

	new_node = (struct interesting_stmts *)xmalloc(sizeof(*new_node));
	new_node->first_stmt = first_stmt;
	new_node->num = num;
	new_node->orig_node = orig_node;
	new_node->next = head;
	return new_node;
}

static void free_interesting_stmts(struct interesting_stmts *head)
{
	while (head) {
		struct interesting_stmts *cur = head->next;
		free(head);
		head = cur;
	}
}

/* This function calls the main recursion function (expand) that duplicates the stmts. Before that it checks the intentional_overflow attribute,
 * it decides whether the duplication is necessary or not. After expand() it changes the orig node to the duplicated node
 * in the original stmt (first stmt) and it inserts the overflow check for the arg of the callee or for the return value.
 */
static struct interesting_stmts *search_interesting_stmt(struct interesting_stmts *head, gimple first_stmt, tree orig_node, unsigned int num)
{
	gcc_assert(orig_node != NULL_TREE);

	if (is_gimple_constant(orig_node))
		return head;

	if (skip_types(orig_node))
		return head;

	if (check_intentional_asm(first_stmt, num) != MARK_NO)
		return head;

	if (SSA_NAME_IS_DEFAULT_DEF(orig_node))
		return head;

	if (skip_asm_cast(orig_node))
		return head;

	if (skip_unnecessary_insertation(orig_node))
		return head;

	return create_interesting_stmts(head, orig_node, first_stmt, num);
}

static void handle_interesting_stmt(struct visited *visited, struct interesting_stmts *head)
{
	struct interesting_stmts *cur;

	for (cur = head; cur; cur = cur->next) {
		tree new_node;

		new_node = expand(visited, cur->orig_node);
		if (new_node == NULL_TREE)
			continue;

		change_orig_node(visited, cur->first_stmt, cur->orig_node, new_node, cur->num);
		check_size_overflow(cur->first_stmt, TREE_TYPE(new_node), new_node, cur->orig_node, BEFORE_STMT);
	}
}

static bool is_interesting_function(const_tree decl, unsigned int num)
{
	const struct size_overflow_hash *hash;

	hash = get_function_hash(get_orig_fndecl(decl));
	if (hash && hash->param & (1U << num))
		return true;
	return get_next_interesting_function(global_next_interesting_function_head, decl, num, YES_SO_MARK) != NULL;
}

// Start stmt duplication on marked function parameters
static struct interesting_stmts *search_interesting_calls(struct interesting_stmts *head, gimple call_stmt)
{
	const_tree fndecl;
	unsigned int i, len;

	len = gimple_call_num_args(call_stmt);
	if (len == 0)
		return head;

	fndecl = gimple_call_fndecl(call_stmt);
	// !!! fnptrs
	if (fndecl == NULL_TREE)
		return head;

	for (i = 0; i < len; i++) {
		tree arg;

		arg = gimple_call_arg(call_stmt, i);
		if (is_gimple_constant(arg))
			continue;
		if (skip_types(arg))
			continue;
		if (is_interesting_function(fndecl, i + 1))
			head = search_interesting_stmt(head, call_stmt, arg, i + 1);
	}

	return head;
}

// Collect interesting stmts for duplication
static void search_interesting_stmts(struct visited *visited)
{
	basic_block bb;
	bool search_ret;
	struct interesting_stmts *head = NULL;

	search_ret = is_interesting_function(current_function_decl, 0);

	FOR_ALL_BB_FN(bb, cfun) {
		gimple_stmt_iterator gsi;

		for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
			tree first_node;
			gimple stmt = gsi_stmt(gsi);

			switch (gimple_code(stmt)) {
			case GIMPLE_ASM:
				if (!is_size_overflow_insert_check_asm(stmt))
					continue;
				first_node = get_size_overflow_asm_input(stmt);
				head = search_interesting_stmt(head, stmt, first_node, 0);
				break;
			case GIMPLE_RETURN:
				if (!search_ret)
					continue;
				first_node = gimple_return_retval(stmt);
				head = search_interesting_stmt(head, stmt, first_node, 0);
				break;
			case GIMPLE_CALL:
				head = search_interesting_calls(head, stmt);
				break;
			default:
				break;
			}
		}
	}

	handle_interesting_stmt(visited, head);
	free_interesting_stmts(head);
}

static struct visited *create_visited(void)
{
	struct visited *new_node;

	new_node = (struct visited *)xmalloc(sizeof(*new_node));
	new_node->stmts = pointer_set_create();
	new_node->my_stmts = pointer_set_create();
	new_node->skip_expr_casts = pointer_set_create();
	new_node->no_cast_check = pointer_set_create();
	return new_node;
}

static void free_visited(struct visited *visited)
{
	pointer_set_destroy(visited->stmts);
	pointer_set_destroy(visited->my_stmts);
	pointer_set_destroy(visited->skip_expr_casts);
	pointer_set_destroy(visited->no_cast_check);

	free(visited);
}

// Remove the size_overflow asm stmt and create an assignment from the input and output of the asm
static void replace_size_overflow_asm_with_assign(gimple asm_stmt, tree lhs, tree rhs)
{
	gimple assign;
	gimple_stmt_iterator gsi;

	// already removed
	if (gimple_bb(asm_stmt) == NULL)
		return;
	gsi = gsi_for_stmt(asm_stmt);

	assign = gimple_build_assign(lhs, rhs);
	gsi_insert_before(&gsi, assign, GSI_SAME_STMT);
	SSA_NAME_DEF_STMT(lhs) = assign;

	gsi_remove(&gsi, true);
}

// Replace our asm stmts with assignments (they are no longer needed and may interfere with later optimizations)
static void remove_size_overflow_asm(gimple stmt)
{
	gimple_stmt_iterator gsi;
	tree input, output;

	if (!is_size_overflow_asm(stmt))
		return;

	if (gimple_asm_noutputs(stmt) == 0) {
		gsi = gsi_for_stmt(stmt);
		ipa_remove_stmt_references(cgraph_get_create_node(current_function_decl), stmt);
		gsi_remove(&gsi, true);
		return;
	}

	input = gimple_asm_input_op(stmt, 0);
	output = gimple_asm_output_op(stmt, 0);
	replace_size_overflow_asm_with_assign(stmt, TREE_VALUE(output), TREE_VALUE(input));
}

static void remove_all_size_overflow_asm(void)
{
	basic_block bb;

	FOR_ALL_BB_FN(bb, cfun) {
		gimple_stmt_iterator si;

		for (si = gsi_start_bb(bb); !gsi_end_p(si); gsi_next(&si))
			remove_size_overflow_asm(gsi_stmt(si));
	}
}

unsigned int size_overflow_transform(struct cgraph_node *node __unused)
{
	struct visited *visited;

#if BUILDING_GCC_VERSION >= 4008
	if (dump_file) {
		fprintf(dump_file, "BEFORE TRANSFORM -------------------------\n");
		size_overflow_dump_function(dump_file, node);
	}
#endif
	visited = create_visited();
	set_dominance_info();

	search_interesting_stmts(visited);

	remove_all_size_overflow_asm();

	unset_dominance_info();
	free_visited(visited);

#if BUILDING_GCC_VERSION >= 4008
	if (dump_file) {
		fprintf(dump_file, "AFTER TRANSFORM -------------------------\n");
		size_overflow_dump_function(dump_file, node);
	}
#endif
	return TODO_dump_func | TODO_verify_stmts | TODO_remove_unused_locals | TODO_update_ssa_no_phi | TODO_ggc_collect | TODO_verify_flow;
}
