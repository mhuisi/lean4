/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <lean/interrupt.h>
#include "kernel/for_each_fn.h"
#include "library/idx_metavar.h"
#include "library/metavar_context.h"
#include "library/replace_visitor.h"

#ifndef LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY
#define LEAN_INSTANTIATE_METAIDX_CACHE_CAPACITY 1024*8
#endif

namespace lean {
static name * g_tmp_prefix = nullptr;

void initialize_idx_metavar() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_idx_metavar() {
    delete g_tmp_prefix;
}

level mk_idx_metauniv(unsigned i) {
    return mk_univ_mvar(name(*g_tmp_prefix, i));
}

expr mk_idx_metavar(unsigned i) {
    return mk_metavar(name(*g_tmp_prefix, i));
}

bool is_idx_metauniv(level const & l) {
    if (!is_mvar(l))
        return false;
    name const & n = mvar_id(l);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(level const & l) {
    lean_assert(is_idx_metauniv(l));
    return mvar_id(l).get_numeral().get_small_value();
}

bool is_idx_metavar(expr const & e) {
    if (!is_metavar(e))
        return false;
    name const & n = mvar_name(e);
    return !n.is_atomic() && n.is_numeral() && n.get_prefix() == *g_tmp_prefix;
}

unsigned to_meta_idx(expr const & e) {
    lean_assert(is_idx_metavar(e));
    return mvar_name(e).get_numeral().get_small_value();
}

bool has_idx_metauniv(level const & l) {
    if (!has_mvar(l))
        return false;
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (!has_mvar(l)) return false;
            if (is_idx_metauniv(l))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_metavar(expr const & e) {
    if (!has_univ_metavar(e) && !has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (!has_univ_metavar(e) && !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e))
                found = true;
            else if (is_constant(e) && std::any_of(const_levels(e).begin(), const_levels(e).end(), has_idx_metauniv))
                found = true;
            else if (is_sort(e) && has_idx_metauniv(sort_level(e)))
                found = true;
            return true;
        });
    return found;
}

bool has_idx_expr_metavar(expr const & e) {
    if (!has_expr_metavar(e))
        return false;
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found || !has_expr_metavar(e)) return false;
            if (is_idx_metavar(e)) found = true;
            return true;
        });
    return found;
}
}
