/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <lean/sstream.h>
#include "util/rb_map.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/trace.h"
#include "library/expr_lt.h"
#include "library/aliases.h"
#include "library/placeholder.h"
#include "library/scoped_ext.h"
#include "library/protected.h"

namespace lean {
struct aliases_ext;
static aliases_ext const & get_extension(environment const & env);
static environment update(environment const & env, aliases_ext const & ext);

struct aliases_ext : public environment_extension {
    struct state {
        bool                  m_in_section;
        name_map<names>       m_aliases;
        name_map<name>        m_inv_aliases;
        state():m_in_section(false) {}

        void add_expr_alias(name const & a, name const & e, bool overwrite) {
            auto it = m_aliases.find(a);
            if (it && !overwrite)
                m_aliases.insert(a, cons(e, filter(*it, [&](name const & t) { return t != e; })));
            else
                m_aliases.insert(a, names(e));
            m_inv_aliases.insert(e, a);
        }
    };

    state       m_state;
    list<state> m_scopes;

    void add_expr_alias(name const & a, name const & e, bool overwrite) {
        m_state.add_expr_alias(a, e, overwrite);
    }

    list<state> add_expr_alias_rec_core(list<state> const & scopes, name const & a, name const & e, bool overwrite) {
        if (empty(scopes)) {
            return scopes;
        } else {
            state s = head(scopes);
            s.add_expr_alias(a, e, overwrite);
            if (s.m_in_section) {
                return cons(s, add_expr_alias_rec_core(tail(scopes), a, e, overwrite));
            } else {
                return cons(s, tail(scopes));
            }
        }
    }

    void add_expr_alias_rec(name const & a, name const & e, bool overwrite = false) {
        if (m_state.m_in_section) {
            m_scopes = add_expr_alias_rec_core(m_scopes, a, e, overwrite);
        }
        add_expr_alias(a, e, overwrite);
    }

    void push(bool in_section) {
        m_scopes = cons(m_state, m_scopes);
        m_state.m_in_section = in_section;
    }

    void pop() {
        m_state  = head(m_scopes);
        m_scopes = tail(m_scopes);
    }

    void for_each_expr_alias(std::function<void(name const &, names const &)> const & fn) {
        m_state.m_aliases.for_each(fn);
    }

    static environment push_scope(environment const & env, io_state const &, scope_kind k) {
        aliases_ext ext = get_extension(env);
        ext.push(k != scope_kind::Namespace);
        environment new_env = update(env, ext);
        return new_env;
    }

    static environment pop_scope(environment const & env, io_state const &, scope_kind) {
        aliases_ext ext = get_extension(env);
        ext.pop();
        return update(env, ext);
    }
};

struct aliases_ext_reg {
    unsigned m_ext_id;
    aliases_ext_reg() {
        register_scoped_ext(aliases_ext::push_scope, aliases_ext::pop_scope);
        m_ext_id = environment::register_extension(new aliases_ext());
    }
};
static aliases_ext_reg * g_ext = nullptr;
static aliases_ext const & get_extension(environment const & env) {
    return static_cast<aliases_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, aliases_ext const & ext) {
    return env.update(g_ext->m_ext_id, new aliases_ext(ext));
}

environment add_expr_alias(environment const & env, name const & a, name const & e, bool overwrite) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias(a, e, overwrite);
    return update(env, ext);
}

environment add_expr_alias_rec(environment const & env, name const & a, name const & e, bool overwrite) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias_rec(a, e, overwrite);
    return update(env, ext);
}

optional<name> is_expr_aliased(environment const & env, name const & t) {
    auto it = get_extension(env).m_state.m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

names get_expr_aliases(environment const & env, name const & n) {
    return names(get_extension(env).m_state.m_aliases.find(n));
}

environment erase_expr_aliases(environment const & env, name const & n) {
    aliases_ext ext = get_extension(env);
    ext.m_state.m_aliases.erase(n);
    return update(env, ext);
}

// Return true iff \c n is (prefix + ex) for some ex in exceptions
bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions) {
    return std::any_of(exceptions, exceptions + num_exceptions, [&](name const & ex) { return (prefix + ex) == n; });
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions, name const * exceptions, bool overwrite) {
    aliases_ext ext = get_extension(env);
    env.for_each_constant([&](constant_info const & info) {
            if (is_prefix_of(prefix, info.get_name()) && !is_exception(info.get_name(), prefix, num_exceptions, exceptions)) {
                name a        = info.get_name().replace_prefix(prefix, new_prefix);
                if (!(is_protected(env, info.get_name()) && a.is_atomic()) &&
                    !(a.is_anonymous()))
                    ext.add_expr_alias(a, info.get_name(), overwrite);
            }
        });
    return update(env, ext);
}

void for_each_expr_alias(environment const & env, std::function<void(name const &, names const &)> const & fn) {
    aliases_ext ext = get_extension(env);
    ext.for_each_expr_alias(fn);
}

void initialize_aliases() {
    g_ext     = new aliases_ext_reg();
}

void finalize_aliases() {
    delete g_ext;
}
}
