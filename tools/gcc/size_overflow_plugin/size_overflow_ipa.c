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

static next_interesting_function_t walk_use_def_next_functions(struct pointer_set_t *visited, next_interesting_function_t next_cnodes_head, const_tree lhs);

next_interesting_function_t global_next_interesting_function_head = NULL;

static struct cgraph_node_hook_list *function_insertion_hook_holder;
static struct cgraph_2node_hook_list *node_duplication_hook_holder;
static struct cgraph_node_hook_list *node_removal_hook_holder;

struct cgraph_node *get_cnode(const_tree fndecl)
{
#if BUILDING_GCC_VERSION <= 4005
	return cgraph_get_node((tree)fndecl);
#else
	return cgraph_get_node(fndecl);
#endif
}

static bool compare_next_interesting_functions(next_interesting_function_t cur_node, const_tree decl, unsigned int num)
{
	if (cur_node->marked == ASM_STMT_SO_MARK)
		return false;

	if (num != CANNOT_FIND_ARG && cur_node->num != num)
		return false;

	return cur_node->decl == decl;
}

/* Find the function with the specified argument in the list
 *   * if marked is ASM_STMT_SO_MARK or YES_SO_MARK then filter accordingly
 *   * if num is CANNOT_FIND_ARG then ignore it
 */
next_interesting_function_t get_next_interesting_function(next_interesting_function_t head, const_tree decl, unsigned int num, enum size_overflow_mark marked)
{
	next_interesting_function_t cur_node;

	if (!head)
		return NULL;

	for (cur_node = head; cur_node; cur_node = cur_node->next) {
		if ((marked == ASM_STMT_SO_MARK || marked == YES_SO_MARK) && cur_node->marked != marked)
			continue;
		if (compare_next_interesting_functions(cur_node, decl, num))
			return cur_node;
	}
	return NULL;
}

tree get_orig_decl_from_global_next_interesting_function_by_str(const_tree clone_fndecl)
{
	next_interesting_function_t cur_node;
	const char *clone_fndecl_name = DECL_NAME_POINTER(clone_fndecl);

	for (cur_node = global_next_interesting_function_head; cur_node; cur_node = cur_node->next) {
		unsigned int fndecl_len = DECL_NAME_LENGTH(cur_node->decl);

		if (!strncmp(DECL_NAME_POINTER(cur_node->decl), clone_fndecl_name, fndecl_len))
			return cur_node->decl;
	}
	return NULL_TREE;
}

static bool is_vararg(const_tree fn, unsigned int num)
{
	const_tree fn_type, last, type;
	tree arg_list;

	if (num == 0)
		return false;
	if (fn == NULL_TREE)
		return false;
	if (TREE_CODE(fn) != FUNCTION_DECL)
		return false;

	fn_type = TREE_TYPE(fn);
	if (fn_type == NULL_TREE)
		return false;

	arg_list = TYPE_ARG_TYPES(fn_type);
	if (arg_list == NULL_TREE)
		return false;
	last = TREE_VALUE(tree_last(arg_list));

	if (TREE_CODE_CLASS(TREE_CODE(last)) == tcc_type)
		type = last;
	else
		type = TREE_TYPE(last);

	gcc_assert(type != NULL_TREE);
	if (type == void_type_node)
		return false;

	return num >= (unsigned int)list_length(arg_list);
}

// Create the main data structure
static next_interesting_function_t create_new_next_interesting_function(next_interesting_function_t head, tree decl, unsigned int num, enum size_overflow_mark marked, next_interesting_function_t orig_next_node)
{
	next_interesting_function_t new_node;

	gcc_assert(TREE_CODE(decl) == FIELD_DECL || TREE_CODE(decl) == FUNCTION_DECL);

	if (is_vararg(decl, num))
		return NULL;

	gcc_assert(num <= MAX_PARAM);

	new_node = (next_interesting_function_t)xmalloc(sizeof(*new_node));
	new_node->decl = decl;
	new_node->num = num;
	new_node->next = head;
	new_node->children = NULL;
	new_node->marked = marked;
	new_node->orig_next_node = orig_next_node;
	return new_node;
}

/* If the interesting function is a clone then find or create its original next_interesting_function_t node
 * and add it to global_next_interesting_function_head
 */
static next_interesting_function_t create_orig_next_node_for_a_clone(const_tree clone_fndecl, unsigned int num, enum size_overflow_mark marked)
{
	next_interesting_function_t orig_next_node;
	tree decl;
	unsigned int orig_num;

	decl = get_orig_fndecl(clone_fndecl);

	if (get_cnode(decl) && !DECL_ARTIFICIAL(clone_fndecl))
		orig_num = get_correct_argnum(get_cnode(clone_fndecl), get_cnode(decl), num);
	else
		orig_num = get_correct_argnum_only_fndecl(clone_fndecl, decl, num);

	if (orig_num == CANNOT_FIND_ARG)
		return NULL;

	orig_next_node = get_next_interesting_function(global_next_interesting_function_head, decl, orig_num, NO_SO_MARK);
	if (orig_next_node)
		return orig_next_node;

	orig_next_node = create_new_next_interesting_function(global_next_interesting_function_head, decl, orig_num, marked, NULL);
	if (!orig_next_node)
		return NULL;

	orig_next_node->next = global_next_interesting_function_head;
	global_next_interesting_function_head = orig_next_node;
	return orig_next_node;
}

// Find or create the next_interesting_function_t node for decl and num
next_interesting_function_t get_and_create_next_node_from_global_next_nodes(tree decl, unsigned int num, enum size_overflow_mark marked, next_interesting_function_t orig_next_node)
{
	next_interesting_function_t cur_next_cnode;

	cur_next_cnode = get_next_interesting_function(global_next_interesting_function_head, decl, num, marked);
	if (cur_next_cnode)
		goto out;

	if (!orig_next_node && made_by_compiler(decl))
		orig_next_node = create_orig_next_node_for_a_clone(decl, num, marked);

	cur_next_cnode = create_new_next_interesting_function(global_next_interesting_function_head, decl, num, marked, orig_next_node);
	if (!cur_next_cnode)
		return NULL;

	cur_next_cnode->next = global_next_interesting_function_head;
	global_next_interesting_function_head = cur_next_cnode;

out:
	if (cur_next_cnode->marked != marked && cur_next_cnode->marked == YES_SO_MARK)
		return cur_next_cnode;
	gcc_assert(cur_next_cnode->marked == marked);
	return cur_next_cnode;
}

static next_interesting_function_t get_and_create_next_node_from_global_next_nodes_stmt(const_gimple stmt, unsigned int num, enum size_overflow_mark marked)
{
	tree decl;

	decl = gimple_call_fndecl(stmt);
	if (decl == NULL_TREE)
		return NULL;
	return get_and_create_next_node_from_global_next_nodes(decl, num, marked, NULL);
}

static next_interesting_function_t handle_function(next_interesting_function_t next_cnodes_head, tree fndecl, const_tree arg)
{
	unsigned int num;
	next_interesting_function_t orig_next_node, new_node;

	gcc_assert(fndecl != NULL_TREE);

	// ignore builtins to not explode coverage (e.g., memcpy)
	if (DECL_BUILT_IN(fndecl))
		return next_cnodes_head;

	// convert arg into its position
	if (arg == NULL_TREE)
		num = 0;
	else
		num = find_arg_number_tree(arg, fndecl);
	if (num == CANNOT_FIND_ARG)
		return next_cnodes_head;

	if (made_by_compiler(fndecl)) {
		orig_next_node = create_orig_next_node_for_a_clone(fndecl, num, NO_SO_MARK);
		if (!orig_next_node)
			return next_cnodes_head;
	} else
		orig_next_node = NULL;
	new_node = create_new_next_interesting_function(next_cnodes_head, fndecl, num, NO_SO_MARK, orig_next_node);
	if (!new_node)
		return next_cnodes_head;
	return new_node;
}

static next_interesting_function_t walk_use_def_next_functions_phi(struct pointer_set_t *visited, next_interesting_function_t next_cnodes_head, const_tree result)
{
	gimple phi = get_def_stmt(result);
	unsigned int i, n = gimple_phi_num_args(phi);

	pointer_set_insert(visited, phi);
	for (i = 0; i < n; i++) {
		tree arg = gimple_phi_arg_def(phi, i);

		next_cnodes_head = walk_use_def_next_functions(visited, next_cnodes_head, arg);
	}

	return next_cnodes_head;
}

static next_interesting_function_t walk_use_def_next_functions_binary(struct pointer_set_t *visited, next_interesting_function_t next_cnodes_head, const_tree lhs)
{
	gimple def_stmt = get_def_stmt(lhs);
	tree rhs1, rhs2;

	rhs1 = gimple_assign_rhs1(def_stmt);
	rhs2 = gimple_assign_rhs2(def_stmt);

	next_cnodes_head = walk_use_def_next_functions(visited, next_cnodes_head, rhs1);
	return walk_use_def_next_functions(visited, next_cnodes_head, rhs2);
}

/* Find all functions that influence lhs
 *
 * Encountered functions are added to the children vector (next_interesting_function_t).
 */
static next_interesting_function_t walk_use_def_next_functions(struct pointer_set_t *visited, next_interesting_function_t next_cnodes_head, const_tree lhs)
{
	const_gimple def_stmt;
	const_tree ssa_var;

	if (skip_types(lhs))
		return next_cnodes_head;

	if (TREE_CODE(lhs) == PARM_DECL)
		return handle_function(next_cnodes_head, current_function_decl, lhs);

	if (TREE_CODE(lhs) != SSA_NAME)
		return next_cnodes_head;

	ssa_var = SSA_NAME_VAR(lhs);
	if (ssa_var != NULL_TREE && TREE_CODE(ssa_var) == PARM_DECL)
		return handle_function(next_cnodes_head, current_function_decl, SSA_NAME_VAR(lhs));

	def_stmt = get_def_stmt(lhs);
	if (!def_stmt)
		return next_cnodes_head;

	if (pointer_set_insert(visited, def_stmt))
		return next_cnodes_head;

	switch (gimple_code(def_stmt)) {
	case GIMPLE_NOP:
		return walk_use_def_next_functions(visited, next_cnodes_head, SSA_NAME_VAR(lhs));
	case GIMPLE_ASM:
		if (is_size_overflow_asm(def_stmt))
			return walk_use_def_next_functions(visited, next_cnodes_head, get_size_overflow_asm_input(def_stmt));
		return next_cnodes_head;
	case GIMPLE_CALL: {
		tree fndecl = gimple_call_fndecl(def_stmt);

		if (fndecl == NULL_TREE)
			return next_cnodes_head;
		return handle_function(next_cnodes_head, fndecl, NULL_TREE);
	}
	case GIMPLE_PHI:
		return walk_use_def_next_functions_phi(visited, next_cnodes_head, lhs);
	case GIMPLE_ASSIGN:
		switch (gimple_num_ops(def_stmt)) {
		case 2:
			return walk_use_def_next_functions(visited, next_cnodes_head, gimple_assign_rhs1(def_stmt));
		case 3:
			return walk_use_def_next_functions_binary(visited, next_cnodes_head, lhs);
		}
	default:
		debug_gimple_stmt((gimple)def_stmt);
		error("%s: unknown gimple code", __func__);
		gcc_unreachable();
	}
}

// Start the search for next_interesting_function_t children based on the (next_interesting_function_t) parent node
static next_interesting_function_t search_next_functions(const_tree node)
{
	struct pointer_set_t *visited;
	next_interesting_function_t next_cnodes_head;

	visited = pointer_set_create();
	next_cnodes_head = walk_use_def_next_functions(visited, NULL, node);
	pointer_set_destroy(visited);

	return next_cnodes_head;
}

// True if child already exists in the next_interesting_function_t children vector
static bool has_child(next_interesting_function_t parent, next_interesting_function_t child)
{
	unsigned int i;
	next_interesting_function_t cur;

	gcc_assert(child);
	// handle recursion
	if (parent->decl == child->decl && parent->num == child->num)
		return true;

#if BUILDING_GCC_VERSION <= 4007
	if (VEC_empty(next_interesting_function_t, parent->children))
		return false;
	FOR_EACH_VEC_ELT(next_interesting_function_t, parent->children, i, cur) {
#else
	FOR_EACH_VEC_SAFE_ELT(parent->children, i, cur) {
#endif
		if (compare_next_interesting_functions(cur, child->decl, child->num))
			return true;
	}
	return false;
}

// Add children to parent and global_next_interesting_function_head
static void collect_data_for_execute(next_interesting_function_t parent, next_interesting_function_t children)
{
	next_interesting_function_t cur = children;

	gcc_assert(parent);

	while (cur) {
		next_interesting_function_t next, child;

		next = cur->next;
		child = get_next_interesting_function(global_next_interesting_function_head, cur->decl, cur->num, NO_SO_MARK);
		if (!child) {
			cur->next = global_next_interesting_function_head;
			global_next_interesting_function_head = cur;
			child = cur;
		}
		// !!! else free?? cur_next_node

		if (!has_child(parent, child)) {
#if BUILDING_GCC_VERSION <= 4007
			VEC_safe_push(next_interesting_function_t, heap, parent->children, child);
#else
			vec_safe_push(parent->children, child);
#endif
		}

		cur = next;
	}
}

static next_interesting_function_t create_parent_next_cnode(const_gimple stmt, unsigned int num)
{
	switch (gimple_code(stmt)) {
	case GIMPLE_ASM:
		return get_and_create_next_node_from_global_next_nodes(current_function_decl, num, ASM_STMT_SO_MARK, NULL);
	case GIMPLE_CALL:
		return get_and_create_next_node_from_global_next_nodes_stmt(stmt, num, NO_SO_MARK);
	case GIMPLE_RETURN:
		return get_and_create_next_node_from_global_next_nodes(current_function_decl, num, NO_SO_MARK, NULL);
	default:
		debug_gimple_stmt((gimple)stmt);
		gcc_unreachable();
	}
}

// Handle potential next_interesting_function_t parent if its argument has an integer type
static void collect_all_possible_size_overflow_fns(const_gimple stmt, unsigned int num)
{
	const_tree start_var;
	next_interesting_function_t children_next_cnode, parent_next_cnode;

	switch (gimple_code(stmt)) {
	case GIMPLE_ASM:
		if (!is_size_overflow_insert_check_asm(stmt))
			return;
		start_var = get_size_overflow_asm_input(stmt);
		gcc_assert(start_var != NULL_TREE);
		break;
	case GIMPLE_CALL:
		start_var = gimple_call_arg(stmt, num - 1);
		break;
	case GIMPLE_RETURN:
		start_var = gimple_return_retval(stmt);
		if (start_var == NULL_TREE)
			return;
		break;
	default:
		debug_gimple_stmt((gimple)stmt);
		gcc_unreachable();
	}

	if (skip_types(start_var))
		return;

	// handle intentional MARK_TURN_OFF
	if (check_intentional_asm(stmt, num) == MARK_TURN_OFF)
		return;

	parent_next_cnode = create_parent_next_cnode(stmt, num);
	if (!parent_next_cnode)
		return;

	children_next_cnode = search_next_functions(start_var);
	collect_data_for_execute(parent_next_cnode, children_next_cnode);
}

// Find potential next_interesting_function_t parents
static void handle_cgraph_node(struct cgraph_node *node)
{
	basic_block bb;
	tree cur_fndecl = NODE_DECL(node);

	set_current_function_decl(cur_fndecl);

	FOR_ALL_BB_FN(bb, cfun) {
		gimple_stmt_iterator gsi;

		for (gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
			gimple stmt = gsi_stmt(gsi);

			switch (gimple_code(stmt)) {
			case GIMPLE_RETURN:
			case GIMPLE_ASM:
				collect_all_possible_size_overflow_fns(stmt, 0);
				break;
			case GIMPLE_CALL: {
				unsigned int i, len;
				tree fndecl = gimple_call_fndecl(stmt);

				if (fndecl != NULL_TREE && DECL_BUILT_IN(fndecl))
					break;

				len = gimple_call_num_args(stmt);
				for (i = 0; i < len; i++)
					collect_all_possible_size_overflow_fns(stmt, i + 1);
				break;
			}
			default:
				break;
			}
		}
	}

	unset_current_function_decl();
}

/* Collect all potentially interesting function parameters and return values of integer types
 * and store their data flow dependencies
 */
static void size_overflow_generate_summary(void)
{
	struct cgraph_node *node;

	size_overflow_register_hooks();

	FOR_EACH_FUNCTION(node) {
		if (!is_valid_cgraph_node(node))
			continue;

		handle_cgraph_node(node);
	}
}

static void size_overflow_function_insertion_hook(struct cgraph_node *node __unused, void *data __unused)
{
	debug_cgraph_node(node);
	gcc_unreachable();
}

/* Handle dst if src is in the global_next_interesting_function_head list.
 * If src is a clone then dst inherits the orig_next_node of src otherwise
 * src will become the orig_next_node of dst.
 */
static void size_overflow_node_duplication_hook(struct cgraph_node *src, struct cgraph_node *dst, void *data __unused)
{
	next_interesting_function_t cur;

	for (cur = global_next_interesting_function_head; cur; cur = cur->next) {
		unsigned int new_argnum;
		next_interesting_function_t clone, orig_next_node;

		if (!compare_next_interesting_functions(cur, NODE_DECL(src), NONE_ARGNUM))
			continue;

		if (!made_by_compiler(cur->decl)) {
			orig_next_node = cur;
			new_argnum = get_correct_argnum(src, dst, cur->num);
		} else if (cur->orig_next_node) {
			orig_next_node = cur->orig_next_node;
			if (DECL_ARTIFICIAL(cur->decl))
				new_argnum = get_correct_argnum_only_fndecl(orig_next_node->decl, NODE_DECL(dst), orig_next_node->num);
			else
				new_argnum = get_correct_argnum(get_cnode(orig_next_node->decl), dst, orig_next_node->num);
		// if gcc loses the original function decl of src then use the clone's argnum
		} else {
			new_argnum = cur->num;
			orig_next_node = NULL;
		}

		if (new_argnum == CANNOT_FIND_ARG)
			continue;

		clone = get_and_create_next_node_from_global_next_nodes(NODE_DECL(dst), new_argnum, cur->marked, orig_next_node);
		gcc_assert(clone);
	}
}

#if BUILDING_GCC_VERSION == 4008 || BUILDING_GCC_VERSION == 4009
static struct cgraph_node *get_prev_next_alias(struct cgraph_node *alias, bool next)
{
	while (alias) {
#if BUILDING_GCC_VERSION == 4008
		symtab_node next_alias;
#else
		symtab_node *next_alias;
#endif

		if (alias->callers)
			return alias;

		if (next)
			next_alias = NODE_SYMBOL(alias)->next_sharing_asm_name;
		else
			next_alias = NODE_SYMBOL(alias)->previous_sharing_asm_name;
		if (!next_alias)
			return NULL;
		alias = cgraph(next_alias);
	}

	return NULL;
}

static struct cgraph_node *get_alias_node(struct cgraph_node *node)
{
	struct cgraph_node *alias = NULL;

	if (!node)
		return NULL;

#if BUILDING_GCC_VERSION == 4008
	if (NODE_SYMBOL(node)->previous_sharing_asm_name && NODE_SYMBOL(node)->previous_sharing_asm_name->symbol.type == SYMTAB_FUNCTION) {
#else
	if (NODE_SYMBOL(node)->previous_sharing_asm_name && NODE_SYMBOL(node)->previous_sharing_asm_name->type == SYMTAB_FUNCTION) {
#endif
		alias = cgraph(NODE_SYMBOL(node)->previous_sharing_asm_name);
		alias = get_prev_next_alias(alias, false);
	}

	if (alias)
		return alias;

#if BUILDING_GCC_VERSION == 4008
	if (NODE_SYMBOL(node)->next_sharing_asm_name && NODE_SYMBOL(node)->next_sharing_asm_name->symbol.type == SYMTAB_FUNCTION) {
#else
	if (NODE_SYMBOL(node)->next_sharing_asm_name && NODE_SYMBOL(node)->next_sharing_asm_name->type == SYMTAB_FUNCTION) {
#endif
		alias = cgraph(NODE_SYMBOL(node)->next_sharing_asm_name);
		alias = get_prev_next_alias(alias, true);
	}

	return alias;
}

// If an interesting function is going away, try to find an alias to preserve its data
void size_overflow_node_removal_hook(struct cgraph_node *node, void *data __unused)
{
	next_interesting_function_t cur;
	const_tree removed_fndecl = NODE_DECL(node);

	if (!global_next_interesting_function_head)
		return;

	for (cur = global_next_interesting_function_head; cur; cur = cur->next) {
		struct cgraph_node *alias_node;

		if (cur->decl != removed_fndecl)
			continue;

		alias_node = get_alias_node(node);
		if (alias_node)
			cur->decl = NODE_DECL(alias_node);
	}
}
#else
void size_overflow_node_removal_hook(struct cgraph_node *node __unused, void *data __unused) {}
#endif

void size_overflow_register_hooks(void)
{
	static bool init_p = false;

	if (init_p)
		return;
	init_p = true;

	function_insertion_hook_holder = cgraph_add_function_insertion_hook(&size_overflow_function_insertion_hook, NULL);
	node_duplication_hook_holder = cgraph_add_node_duplication_hook(&size_overflow_node_duplication_hook, NULL);
	node_removal_hook_holder = cgraph_add_node_removal_hook(&size_overflow_node_removal_hook, NULL);
}

static void set_yes_so_mark(next_interesting_function_t next_node)
{
	next_node->marked = YES_SO_MARK;
	// mark the orig decl as well if it's a clone
	if (next_node->orig_next_node)
		next_node->orig_next_node->marked = YES_SO_MARK;
}

// Determine if the function is already in the hash table
static bool is_marked_fn(next_interesting_function_t next_node)
{
	const struct size_overflow_hash *hash;
	unsigned int num;
	const_tree decl;

	if (next_node->marked != NO_SO_MARK)
		return true;

	if (next_node->orig_next_node) {
		decl = next_node->orig_next_node->decl;
		num = next_node->orig_next_node->num;
	} else {
		decl = next_node->decl;
		num = next_node->num;
	}

	hash = get_function_hash(decl);
	if (!hash)
		return false;

	if (!(hash->param & (1U << num)))
		return false;

	set_yes_so_mark(next_node);
	return true;
}

// Do a depth-first recursive dump of the next_interesting_function_t children vector
static void print_missing_functions(struct pointer_set_t *visited, next_interesting_function_t parent)
{
	unsigned int i;
	next_interesting_function_t child;

	gcc_assert(parent);
	print_missing_function(parent);

#if BUILDING_GCC_VERSION <= 4007
	if (VEC_empty(next_interesting_function_t, parent->children))
		return;
	FOR_EACH_VEC_ELT(next_interesting_function_t, parent->children, i, child) {
#else
	FOR_EACH_VEC_SAFE_ELT(parent->children, i, child) {
#endif
		// since the parent is a marked function we will set YES_SO_MARK on the children to transform them as well
		child->marked = YES_SO_MARK;
		if (!pointer_set_insert(visited, child))
			print_missing_functions(visited, child);
	}
}

// Print all missing interesting functions
static unsigned int size_overflow_execute(void)
{
	struct pointer_set_t *visited;
	next_interesting_function_t cur_global;

	if (!global_next_interesting_function_head)
		return 0;

	visited = pointer_set_create();

	for (cur_global = global_next_interesting_function_head; cur_global; cur_global = cur_global->next) {
		if (is_marked_fn(cur_global))
			print_missing_functions(visited, cur_global);
	}

//	if (in_lto_p)
//		print_next_interesting_functions(global_next_interesting_function_head, false);

	pointer_set_destroy(visited);

	return 0;
}

// Omit the IPA/LTO callbacks until https://gcc.gnu.org/bugzilla/show_bug.cgi?id=61311 gets fixed (license concerns)
#if BUILDING_GCC_VERSION >= 4008
void __attribute__((weak)) size_overflow_write_summary_lto(void) {}
void __attribute__((weak)) size_overflow_write_optimization_summary_lto(void) {}
#elif BUILDING_GCC_VERSION >= 4006
void __attribute__((weak)) size_overflow_write_summary_lto(cgraph_node_set set, varpool_node_set vset) {}
void __attribute__((weak)) size_overflow_write_optimization_summary_lto(cgraph_node_set set, varpool_node_set vset) {}
#else
void __attribute__((weak)) size_overflow_write_summary_lto(cgraph_node_set set) {}
void __attribute__((weak)) size_overflow_write_optimization_summary_lto(cgraph_node_set set) {}
#endif

void __attribute__((weak)) size_overflow_read_summary_lto(void) {}

#if BUILDING_GCC_VERSION >= 4009
static const struct pass_data size_overflow_functions_pass_data = {
#else
static struct ipa_opt_pass_d size_overflow_functions_pass = {
	.pass = {
#endif
		.type			= IPA_PASS,
		.name			= "size_overflow_functions",
#if BUILDING_GCC_VERSION >= 4008
		.optinfo_flags		= OPTGROUP_NONE,
#endif
#if BUILDING_GCC_VERSION >= 4009
		.has_gate		= false,
		.has_execute		= true,
#else
		.gate			= NULL,
		.execute		= size_overflow_execute,
		.sub			= NULL,
		.next			= NULL,
		.static_pass_number	= 0,
#endif
		.tv_id			= TV_NONE,
		.properties_required	= 0,
		.properties_provided	= 0,
		.properties_destroyed	= 0,
		.todo_flags_start	= 0,
		.todo_flags_finish	= 0,
#if BUILDING_GCC_VERSION < 4009
	},
	.generate_summary		= size_overflow_generate_summary,
	.write_summary			= size_overflow_write_summary_lto,
	.read_summary			= size_overflow_read_summary_lto,
#if BUILDING_GCC_VERSION >= 4006
	.write_optimization_summary	= size_overflow_write_optimization_summary_lto,
	.read_optimization_summary	= size_overflow_read_summary_lto,
#endif
	.stmt_fixup			= NULL,
	.function_transform_todo_flags_start		= 0,
	.function_transform		= size_overflow_transform,
	.variable_transform		= NULL,
#endif
};

#if BUILDING_GCC_VERSION >= 4009
namespace {
class size_overflow_functions_pass : public ipa_opt_pass_d {
public:
	size_overflow_functions_pass() : ipa_opt_pass_d(size_overflow_functions_pass_data,
			 g,
			 size_overflow_generate_summary,
			 size_overflow_write_summary_lto,
			 size_overflow_read_summary_lto,
			 size_overflow_write_optimization_summary_lto,
			 size_overflow_read_summary_lto,
			 NULL,
			 0,
			 size_overflow_transform,
			 NULL) {}
	unsigned int execute() { return size_overflow_execute(); }
};
}

opt_pass *make_size_overflow_functions_pass(void)
{
	return new size_overflow_functions_pass();
}
#else
struct opt_pass *make_size_overflow_functions_pass(void)
{
	return &size_overflow_functions_pass.pass;
}
#endif

static bool size_overflow_free(void)
{
	next_interesting_function_t head = global_next_interesting_function_head;

	while (head) {
		next_interesting_function_t cur = head->next;
		free(head);
		head = cur;
	}

	global_next_interesting_function_head = NULL;

	return true;
}

#if BUILDING_GCC_VERSION >= 4009
static const struct pass_data size_overflow_free_pass_data = {
#else
static struct gimple_opt_pass size_overflow_free_pass = {
	.pass = {
#endif
		.type			= GIMPLE_PASS,
		.name			= "size_overflow_free",
#if BUILDING_GCC_VERSION >= 4008
		.optinfo_flags		= OPTGROUP_NONE,
#endif
#if BUILDING_GCC_VERSION >= 4009
		.has_gate		= true,
		.has_execute		= false,
#else
		.gate			= size_overflow_free,
		.execute		= NULL,
		.sub			= NULL,
		.next			= NULL,
		.static_pass_number	= 0,
#endif
		.tv_id			= TV_NONE,
		.properties_required	= 0,
		.properties_provided	= 0,
		.properties_destroyed	= 0,
		.todo_flags_start	= 0,
		.todo_flags_finish	= 0,
#if BUILDING_GCC_VERSION < 4009
	}
#endif
};

#if BUILDING_GCC_VERSION >= 4009
namespace {
class size_overflow_free_pass : public gimple_opt_pass {
public:
	size_overflow_free_pass() : gimple_opt_pass(size_overflow_free_pass_data, g) {}
	opt_pass * clone() { return new size_overflow_free_pass(); }
	bool gate() { return size_overflow_free(); }
	unsigned int execute() { return 0; }
};
}

opt_pass *make_size_overflow_free_pass(void)
{
	return new size_overflow_free_pass();
}
#else
struct opt_pass *make_size_overflow_free_pass(void)
{
	return &size_overflow_free_pass.pass;
}
#endif
