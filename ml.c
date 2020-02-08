#include <ctype.h>
#include <iso646.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef union value_t value_t;
typedef struct env_t env_t;
typedef struct types_t { struct type_t *type; struct types_t *next; } types_t;
typedef struct sub_t { struct type_t *from, *to; struct sub_t *next; } sub_t;
typedef struct type_t {
    bool variable;
    int uid;
    struct type_t *instance;
    char *name;
    types_t *args;
} type_t;
union value_t {
    bool b;
    int i;
    unsigned char *s;
    value_t *t;
    struct list_t *l;
    struct { int op; char *param; struct exp_t *body; env_t *env; } f;
    struct { int op, i, n; struct list_t *args; } h;
};
struct env_t { char *name; type_t *type; value_t value; env_t *tl; };
typedef struct list_t { value_t hd; struct list_t *tl; } list_t;
typedef struct exp_t exp_t;
struct exp_t {
    enum { ENIL, EBOOL, EINT, ESTRING, ETUPLE, ECONS, ENAME, EFUN, EAPP,
        EIF, EMATCH, ELET, ELETREC, } op;
    int line;
    type_t *type;
    union { int integer;
            char *string, *name;
            struct { char *param; exp_t *body; } fun;
            struct { int n; exp_t **items; } tuple;
            struct { exp_t *lhs, *rhs; } app, cons;
            struct { exp_t *cond, *t, *f; } cond;
            struct rule_t { exp_t *lhs, *rhs; struct rule_t *next; } rule;
            struct { exp_t *cond; struct rule_t *rule; } match;
            struct { char *name; exp_t *value, *body; } let;
            struct dec_t { char *name; type_t *type; exp_t *value; struct dec_t *tl; } dec;
            struct { struct dec_t *decs; exp_t *body; } letrec;
    };
};
enum { TEOF, TINT, TSTR, TNAME, TLP, TRP, TLB, TRB, TCOMMA, TBAR, TSEMI,
        TFALSE, TTRUE, TFUN, TARROW, TIF, TTHEN, TELSE, TEQ, TLET, TREC,
        TIN, TAND, TOR, TOP, };
char    source[65536], *src=source, tbuf[sizeof source], *tstr;
int     token, peeked, line=1, tint;
char    *pun = "()[],|;", *idchr="_!?'", *opchr="@$%^&*-+=.<>/:", *ignore="_";
char    *resv[] = {
            "end", "int", "string", "name", "(", ")", "[", "]", ",", "|", ";",
            "false", "true", "fun", "->", "if", "then", "else", "=",
            "let", "rec", "in", "and", "or", "__op", 0};
struct op_t { int level; char *name; } _ops[256], *ops=_ops-1, *last_op;
char    *interns[65536];
int     ninterns;
type_t  *bool_type, *int_type, *str_type, *tuple_type, *list_type, *fun_type;
value_t nilv={.l=0}, falsev={.b=false}, truev={.b=true};
#define new(type, ...) copy(sizeof(type), &(type){__VA_ARGS__})
#define exp(head, ...) new(exp_t, head, line, __VA_ARGS__)
void *copy(size_t size, void *p) { return memmove(malloc(size), p, size); }
void panic(char *msg, ...);
type_t *new_type_var() { static int uid;  return new(type_t, .variable=true, .uid=++uid); }
type_t *new_type_oper(char *name, types_t *args) {
    return new(type_t, .name=name, .args=args);
}
type_t *new_list_type(type_t *t) {
    return new_type_oper(list_type->name, new(types_t, t, 0));
}
type_t *new_fun_type(type_t *t, type_t *u) {
    return new_type_oper(fun_type->name, new(types_t, t, new(types_t, u, 0)));
}
type_t *prune(type_t *t) {
    return t->variable and t->instance ? (t->instance = prune(t->instance)) : t;
}
bool in_type(type_t *var, type_t *type) {
    type = prune(type);
    if (type->variable) return var == type;
    for (types_t *i = type->args; i; i = i->next)
        if (in_type(var, i->type)) return true;
    return false;
}
type_t *fresh_var(type_t *var, sub_t **subs) {
    for (sub_t *i = *subs; i; i = i->next)
        if (i->from == var) return i->to;
    return (*subs = new(sub_t, var, new_type_var(), *subs))->to;
}
type_t *fresh(type_t *t, types_t *nongeneric, sub_t **subs);
types_t *fresh_args(types_t *args, types_t *nongeneric, sub_t **subs) {
    if (not args) return 0;
    type_t *t = fresh(args->type, nongeneric, subs);
    return new(types_t, t, fresh_args(args->next, nongeneric, subs));
}
type_t *fresh(type_t *t, types_t *nongeneric, sub_t **subs) {
    t = prune(t);
    if (t->variable)
        for (types_t *i = nongeneric; i; i = i->next)
            if (in_type(t, i->type)) return t;
    if (t->variable) return fresh_var(t, subs);
    if (not t->args) return t;
    return new_type_oper(t->name, fresh_args(t->args, nongeneric, subs));
}
bool _unify(type_t *t, type_t *u) {
    t = prune(t);
    u = prune(u);
    if (t->variable)
        if (in_type(t, u)) return t == u;
        else return t->instance = u, true;
    else if (u->variable) return _unify(u, t);
    if (t->name != u->name) return false;
    for (types_t *a=t->args, *b=u->args; ; a=a->next, b=b->next)
        if (not a and b or a and not b) return false;
        else if (not a and not b) return true;
        else if (not _unify(a->type, b->type)) return false;
}
type_t *unify(exp_t *e, type_t *t, type_t *u) {
    if (not _unify(t, u)) panic("LINE %d: TYPE %t VS %t", e->line, t, u);
    return prune(t);
}
void print_type(type_t *type) {
    type = prune(type);
    if (type->variable) { printf("'%d", type->uid); return; }
    if (type->name == fun_type->name) {
        type_t *u = prune(type->args->type);
        if (u->name == fun_type->name) putchar('(');
        print_type(u);
        if (u->name == fun_type->name) putchar(')');
        printf("->");
        print_type(type->args->next->type);
    } else if (type->name == tuple_type->name) {
        putchar('(');
        for (types_t *i = type->args; i; i = i->next)
            print_type(i->type), printf(i->next ? "," : "");
        putchar(')');
    } else if (type->name == list_type->name) {
        putchar('['); print_type(type->args->type); putchar(']');
    } else {
        if (type->args) putchar('(');
        printf("%s", type->name);
        for (types_t *i = type->args; i; i = i->next)
            putchar(' '), print_type(i->type);
        if (type->args) putchar(')');
    }
}
void print(value_t x, type_t *type) {
    type = prune(type);
    if (type == bool_type) printf(x.b ? "true" : "false");
    else if (type == int_type) printf("%d", x.i);
    else if (type == str_type) printf("%s", x.s);
    else if (type->name == tuple_type->name) {
        int i = 0;
        putchar('(');
        for (types_t *t = type->args; t; t = t->next)
            print(x.t[i++], t->type), printf(t->next ? "," : "");
        putchar(')');
    } else if (type->name == list_type->name) {
        putchar('[');
        for (list_t *i = x.l; i; i = i->tl)
            print(i->hd, prune(type->args->type)),
            i->tl ? putchar(' ') : 0;
        putchar(']');
    } else if (type->name == fun_type->name)
        if (x.f.op) printf("fun _%d->...", x.f.op);
        else printf("fun %s->...", x.f.param);
    else panic("PRINT(*,%s)", type->name ? type->name : "(variable)");
}
value_t newi(int x) { return (value_t){.i=x}; }
value_t news(char *x) { return (value_t){.s=x}; }
value_t newt(value_t *x) { return (value_t){.t=x}; }
value_t newl(list_t *x) { return (value_t){.l=x}; }
value_t newf(char *param, exp_t *body, env_t *env) {
    return (value_t){.f={0, param, body, env}};
}
value_t newh(int op, int n) { return (value_t){.h={op, 0, n, 0}}; }
list_t *cons(value_t hd, list_t *tl) { return new(list_t, hd, tl); }
void panic(char *msg, ...) {
    printf("PANIC - ");
    va_list ap; va_start(ap, msg);
    for ( ; *msg; msg++)
        if (*msg != '%') putchar(*msg);
        else switch (*++msg) {
        case 'd':   printf("%d", va_arg(ap, int)); break;
        case 's':   printf("%s", va_arg(ap, char*)); break;
        case 't':   print_type(va_arg(ap, type_t*)); break;
        }
    puts(""); exit(2);
}
void syntax(int line, char *msg, ...) {
    va_list ap; va_start(ap, msg);
    printf("error %d: ", line);
    vprintf(msg, ap), puts(".");
    exit(1);
}
char *intern(char *txt) {
    for (int i = 0; i < ninterns; i++)
        if (not strcmp(interns[i], txt)) return interns[i];
    return interns[ninterns++] = strdup(txt);
}
int next() {
    if (peeked) return peeked = false, token;
    for ( ; isspace(*src) or *src == '#'; src++)
        if (*src == '\n') line++;
        else if (*src == '#') while (src[1] and src[1] != '\n') src++;
    if (not *src) return token = TEOF;
    char *p, *t=tbuf;
    if (p = strchr(pun, *src)) return src++, token = TLP + p - pun;
    if (isdigit(src[*src == '-']))
        return tint = strtoul(src, &src, 10), token = TINT;
    if (*src == '"')
        for (char quote = *src++; ; src++)
            if (*src == quote)
                return src++, *t=0, tstr=intern(tbuf), token=TSTR;
            else if (not *src) syntax(line, "unclosed string");
            else if (*src == '\\') {
                char *p = strchr("a\ab\be\033n\nr\rt\t", *++src);
                *t++ = p ? p[1] : *src;
            } else *t++ = *src;
    while (isalnum(*src) or (unsigned)*src > 127 or *src and strchr(idchr,*src))
        *t++ = *src++;
    if (t == tbuf) while (*src and strchr(opchr, *src)) *t++ = *src++;
    if (t == tbuf) syntax(line, "bad token `%c`", *src);
    *t=0, tstr=intern(tbuf);
    for (int i = TFALSE; resv[i]; i++) if (resv[i] == tstr) return token=i;
    return token=TNAME;
}
bool peek(int t) { next(); peeked = true; return t == token; }
bool want(int t) { next(); peeked = t != token; return t == token; }
void need(int t) { if (not want(t)) syntax(line, "need %s", resv[t]); }
exp_t *_exp(), *_pattern();
struct op_t *operator(int level, char *name) {
    for (struct op_t *i = ops; i >= _ops; i--)
        if (i->name == name and (not level or abs(i->level) == level))
            return last_op=i;
    return 0;
}
exp_t *prefixed(int t) { need(t); return _exp(); }
exp_t *_list() {
    exp_t *hd = _exp();
    exp_t *tl = want(TCOMMA) ? _list() : exp(ENIL);
    return exp(ECONS, .cons={hd, tl});
}
exp_t *_function() {
    if (want(TNAME)) {
        char *name = tstr;
        return exp(EFUN, .fun={name, _function()});
    } else { if (not want(TEQ)) need(TARROW); return _exp(); }
}
exp_t *atom(bool required, bool is_pattern) {
    exp_t *e, **es = 0;
    switch (next()) {
    case TFALSE:    return exp(EBOOL, .integer=false);
    case TTRUE:     return exp(EBOOL, .integer=true);
    case TINT:      return exp(EINT, .integer=tint);
    case TSTR:      return exp(ESTRING, .string=tstr);
    case TLP: {     int n = 0;
                    do {    if (peek(TRP)) break;
                            es = realloc(es, ++n * sizeof *es);
                            es[n - 1] = is_pattern ? _pattern() : _exp();
                    } while (want(TCOMMA));
                    need(TRP);
                    if (n == 1) return es[0];
                    return exp(ETUPLE, .tuple={n, es}); }
    case TLB:       e = peek(TRB) ? exp(ENIL) : _list(); need(TRB); return e;
    case TNAME:     if (not required and operator(0, tstr)) goto abort;
                    return exp(ENAME, .name=tstr);
    case TFUN:      if (is_pattern) goto abort; return _function();
    default:        abort: peeked = true;
                    if (required) syntax(line, "need expression");
                    return 0;
    }
}
exp_t *appexp() {
    exp_t *e = atom(true, false), *rhs;
    while (rhs = atom(false, false)) e = exp(EAPP, .app={e, rhs});
    return e;
}
exp_t *infexp(int level) {
    if (level == 10) return appexp();
    exp_t *e = infexp(level + 1);
    while ((peek(TNAME) or peek(TAND) or peek(TOR)) and operator(level, tstr)) {
        next();
        if (token == TAND or token == TOR) {
            bool is_and = token == TAND;
            exp_t *t = is_and ? infexp(level) : exp(EBOOL, .integer=true);
            exp_t *f = is_and ? exp(EBOOL, .integer=false) : infexp(level);
            e = exp(EIF, .cond={e, t, f});
        } else {
            exp_t *lhs = exp(EAPP, .app={exp(ENAME, .name=tstr), e});
            exp_t *rhs = infexp(last_op->level < 0 ? level : level + 1);
            e = exp(EAPP, .app={lhs, rhs});
        }
    }
    return e;
}
exp_t *_pattern() {
    exp_t *e = atom(true, true);
    if (peek(TNAME) and not strcmp(tstr, ":") and want(TNAME))
        return exp(ECONS, .cons={e, _pattern()});
    return e;
}
struct rule_t *_rules() {
    if (not want(TBAR)) return 0;
    exp_t *lhs = _pattern();
    exp_t *rhs = prefixed(TARROW);
    struct rule_t *next = _rules();
    return new(struct rule_t, lhs, rhs, next);
}
struct dec_t *_decs() {
    char *name = (need(TNAME), tstr);
    exp_t *value = peek(TNAME) ? _function() : prefixed(TEQ);
    struct dec_t *tl = want(TSEMI) and not peek(TIN) ? _decs() : 0;
    return new(struct dec_t, name, 0, value, tl);
}
struct exp_t *_let() {
    if (want(TOP)) {
        int level, n = 0;
        while (want(TINT)) {
            level = tint;
            while (want(TNAME)) *++ops = (struct op_t){level, tstr}, n++;
        }
        exp_t *e = want(TLET) ? _let() : prefixed(TIN);
        return ops -= n, e;
    } else if (want(TREC)) {
        struct dec_t *decs = _decs();
        exp_t *body = want(TLET) ? _let() : prefixed(TIN);
        return exp(ELETREC, .letrec={decs, body});
    } else if (want(TNAME)) {
        char *name = tstr;
        exp_t *value = peek(TNAME) ? _function() : prefixed(TEQ);
        exp_t *body = want(TLET) ? _let() : prefixed(TIN);
        return exp(ELET, .let={name, value, body});
    } else {
        exp_t *pat = _pattern();
        exp_t *value = prefixed(TEQ);
        exp_t *body = want(TLET) ? _let() : prefixed(TIN);
        struct rule_t *rule = new(struct rule_t, pat, body, 0);
        return exp(EMATCH, .match={value, rule});
    }
}
exp_t *_exp() {
    if (want(TIF)) {
        exp_t *cond = _exp();
        if (peek(TBAR)) {
            struct rule_t *rules = _rules();
            return exp(EMATCH, .match={cond, rules});
        }
        exp_t *t = prefixed(TTHEN);
        exp_t *f = prefixed(TELSE);
        return exp(EIF, .cond={cond, t, f});
    } else if (want(TLET)) return _let();
    else return infexp(1);
}
env_t *lookup(exp_t *e, env_t *env, char *name) {
    if (not env) panic("LINE %d: %s NOT DEFINED", e->line, name);
    return env->name == name ? env : lookup(e, env->tl, name);
}
value_t set(exp_t *e, env_t *env, char *name, value_t value) {
    if (not env) panic("LINE %d: %s NOT DEFINED", e->line, name);
    return env->name == name ?
        (env->value = value): set(e, env->tl, name, value);
}
env_t *define(env_t *env, char *name, type_t *type, value_t value) {
    return new(env_t, name, type, value, env);
}
type_t *assign(env_t *env, exp_t *e, types_t *ng);
env_t *assign_pat(env_t *env, exp_t *e, types_t **ng) {
    types_t *args = 0;
    switch (e->op) {
    case ENIL: case EBOOL: case EINT: case ESTRING:
                    return assign(env, e, *ng), env;
    case ETUPLE:    for (int i = e->tuple.n - 1; i >= 0; i--) {
                        env = assign_pat(env, e->tuple.items[i], ng);
                        args = new(types_t, e->tuple.items[i]->type, args);
                    }
                    e->type = new_type_oper(tuple_type->name, args);
                    return env;
    case ECONS:     env = assign_pat(env, e->cons.lhs, ng);
                    env = assign_pat(env, e->cons.rhs, ng);
                    e->type = unify(e,  e->cons.rhs->type,
                                        new_list_type(e->cons.lhs->type));
                    return env;
    case ENAME:     e->type = new_type_var();
                    *ng = new(types_t, e->type, *ng);
                    return define(env, e->name, e->type, nilv);
    default:        panic("ASSIGN_PAT(%d)", e->op); return 0;
    }
}
type_t *assign(env_t *env, exp_t *e, types_t *ng) {
    type_t *t, *u, *v;
    sub_t *subs = 0;
    types_t *old_ng = ng, *args = 0;
    switch (e->op) {
    case ENIL:      return e->type = new_list_type(new_type_var());
    case EBOOL:     return e->type = bool_type;
    case EINT:      return e->type = int_type;
    case ESTRING:   return e->type = str_type;
    case ETUPLE:    for (int i = e->tuple.n - 1; i >= 0; i--) {
                        assign(env, e->tuple.items[i], ng);
                        args = new(types_t, e->tuple.items[i]->type, args);
                    }
                    return e->type = new_type_oper(tuple_type->name, args);
    case ECONS:     t = assign(env, e->cons.lhs, ng);
                    u = assign(env, e->cons.rhs, ng);
                    return e->type = unify(e, u, new_list_type(t));
    case ENAME:     t = lookup(e, env, e->name)->type;
                    return e->type = fresh(t, ng, &subs);
    case EFUN:      t = new_type_var();
                    ng = new(types_t, t, ng);
                    env = define(env, e->fun.param, t, nilv);
                    u = assign(env, e->fun.body, ng);
                    return e->type = new_fun_type(t, u);
    case EAPP:      t = assign(env, e->app.lhs, ng);
                    u = assign(env, e->app.rhs, ng);
                    v = new_type_var();
                    unify(e, t, new_fun_type(u, v));
                    return e->type = v;
    case EIF:       t = assign(env, e->cond.cond, ng);
                    unify(e->cond.cond, t, bool_type);
                    u = assign(env, e->cond.t, ng);
                    v = assign(env, e->cond.f, ng);
                    return e->type = unify(e, u, v);
    case EMATCH:    v = 0; t = assign(env, e->match.cond, ng);
                    for (struct rule_t *i = e->match.rule; i; i = i->next) {
                        types_t *rhs_ng = ng;
                        env_t *rhs_env = assign_pat(env, i->lhs, &rhs_ng);
                        unify(i->lhs, t, i->lhs->type),
                        u = assign(rhs_env, i->rhs, rhs_ng),
                        v = not v ? u : unify(i->rhs, v, u);
                    } return e->type = v;
    case ELET:      t = assign(env, e->let.value, ng);
                    env = define(env, e->let.name, t, nilv);
                    return e->type = assign(env, e->let.body, ng);
    case ELETREC:   for (struct dec_t *i = e->letrec.decs; i; i = i->tl) {
                        i->type = new_type_var();
                        ng = new(types_t, i->type, ng);
                        env = define(env, i->name, i->type, nilv);
                    }
                    for (struct dec_t *i = e->letrec.decs; i; i = i->tl)
                        unify(i->value, i->type,assign(env, i->value, ng));
                    return e->type = assign(env, e->letrec.body, old_ng);
    default:        panic("ASSIGN(%d)", e->op); return 0;
    }
}
enum { OMUL=1,ODIV,OREM,OADD,OSUB,OCONS,OSEQ,OEQ,ONE,OLE,OGE,OLT,OGT,OPRN,
        OEQUALS,OSUBS,OLENS,OIMPLODE,OEXPLODE,OCHR,OORD, };
value_t host(int op, list_t *args, value_t x) {
    value_t w = args ? args->hd : nilv;
    value_t v = args and args->tl ? args->tl->hd : nilv;
    switch (op) {
    case OMUL:  return newi(w.i * x.i);
    case ODIV:  if (x.i == 0) panic("DIVISION BY ZERO"); return newi(w.i / x.i);
    case OREM:  if (x.i == 0) panic("DIVISION BY ZERO"); return newi(w.i % x.i);
    case OADD:  return newi(w.i + x.i);
    case OSUB:  return newi(w.i - x.i);
    case OCONS: return newl(cons(w, x.l));
    case OSEQ:  return not strcmp(w.s, x.s) ? truev : falsev;
    case OEQ:   return w.i == x.i ? truev : falsev;
    case ONE:   return w.i != x.i ? truev : falsev;
    case OLE:   return w.i <= x.i ? truev : falsev;
    case OGE:   return w.i >= x.i ? truev : falsev;
    case OLT:   return w.i < x.i ? truev : falsev;
    case OGT:   return w.i > x.i ? truev : falsev;
    case OPRN:  printf("%s", x.s); return x;
    case OEQUALS:   return not strcmp(w.s, x.s) ? truev : falsev;
    case OSUBS: {   int len = strlen(x.s);
                    v.i += v.i < 0 ? len + 1 : 0; w.i += w.i < 0 ? len + 1 : 0;
                    if (v.i < 0 or w.i < v.i or w.i > len)
                        panic("INDEX %d:%d", v.i, w.i);
                    if (v.i == w.i) return news(interns[x.s[v.i]]);
                    char *txt = calloc(1, w.i - v.i + 1);
                    return news(memmove(txt, x.s + v.i, w.i - v.i)); }
    case OLENS:     return newi(strlen(x.s));
    case OIMPLODE:  {   char *out = 0;
                        int total = 0, n;
                        for (list_t *i = x.l; i; i = i->tl) {
                            n = strlen(i->hd.s);
                            out = realloc(out, (total += n) + 1);
                            strcat(&out[total - n], i->hd.s);
                        } return news(out ? out : interns[0]); }
    case OEXPLODE:  {   list_t *out = 0;
                        for (char *s = strchr(x.s, 0) - 1; s >= x.s; s--)
                            out = cons(news(interns[*s]), out);
                        return newl(out); }
    case OCHR:  if (x.i < 0 or x.i > 255) panic("%d NOT CHAR", x.i);
                return news(interns[x.i]);
    case OORD:  return newi(*x.s);
    default:    return panic("HOST(%d)", op), nilv;
    }
}
env_t *match(env_t *env, exp_t *e, value_t x) {
    switch (e->op) {
    case ENIL:      return x.l == 0 ? env : 0;
    case EBOOL:     return x.b == e->integer ? env : 0;
    case EINT:      return x.i == e->integer ? env : 0;
    case ESTRING:   return not strcmp(x.s, e->string) ? env : 0;
    case ETUPLE:    for (int i = 0; i < e->tuple.n; i++)
                        if (env = match(env, e->tuple.items[i], x.t[i]));
                        else return 0;
                    return env;
    case ECONS: return  x.l and (env = match(env, e->cons.lhs, x.l->hd)) and
                        (env = match(env, e->cons.rhs, newl(x.l->tl)))
                        ? env : 0;
    case ENAME: return e->name == ignore ? env : define(env, e->name, 0, x);
    default:    panic("MATCH(%d)", e->op); return 0;
    }
}
value_t eval(env_t *env, exp_t *e) {
    value_t x, y, *xs;
    tail:
    switch (e->op) {
    case ENIL:      return newl(0);
    case EBOOL:     return e->integer ? truev : falsev;
    case EINT:      return newi(e->integer);
    case ESTRING:   return news(e->string);
    case ETUPLE:    xs = malloc(e->tuple.n * sizeof *xs);
                    for (int i = 0; i < e->tuple.n; i++)
                        xs[i] = eval(env, e->tuple.items[i]);
                    return newt(xs);
    case ECONS:     x = eval(env, e->cons.lhs);
                    y = eval(env, e->cons.rhs);
                    return newl(cons(x, y.l));
    case ENAME:     return lookup(e, env, e->name)->value;
    case EFUN:      return newf(e->fun.param, e->fun.body, env);
    case EAPP:      x = eval(env, e->app.lhs);
                    y = eval(env, e->app.rhs);
                    if (x.f.op) {
                        if (++x.h.i == x.h.n) return host(x.h.op, x.h.args, y);
                        x.h.args = cons(y, x.h.args);
                        return x;
                    }
                    env = define(x.f.env, x.f.param, 0, y);
                    e = x.f.body; goto tail;
    case EIF:       x = eval(env, e->cond.cond);
                    e = x.b ? e->cond.t : e->cond.f; goto tail;
    case EMATCH:    x = eval(env, e->match.cond);
                    env_t *new_env;
                    for (struct rule_t *i = e->match.rule; i; i = i->next)
                        if (new_env = match(env, i->lhs, x))
                            { e = i->rhs; env = new_env; goto tail; }
                    return panic("LINE %d: NO_MATCH", e->line, x), nilv;
    case ELET:      x = eval(env, e->let.value);
                    env = define(env, e->let.name, 0, x);
                    e = e->let.body; goto tail;
    case ELETREC:   for (struct dec_t *i = e->letrec.decs; i; i = i->tl)
                        env = define(env, i->name, 0, nilv);
                    for (struct dec_t *i = e->letrec.decs; i; i = i->tl)
                        set(i->value, env, i->name, eval(env, i->value));
                    e = e->letrec.body; goto tail;
    default:        return panic("EVAL(%d)", e->op), nilv;
    }
}
type_t *foldt(type_t **t) { return t[1] ? new_fun_type(*t, foldt(t + 1)) : *t; }
#define HOST(name, op, level, ...)\
    env = define(env, intern(#name),\
        foldt((type_t*[]){__VA_ARGS__,0}),\
        newh(op, -1 + sizeof (type_t*[]){__VA_ARGS__} / sizeof *(type_t*[]){__VA_ARGS__}));\
    if (level) *++ops = (struct op_t){level, intern(#name)}; else {}
#define IBIN(name,op,level) HOST(name,op,level,int_type,int_type,int_type)
#define ICMP(name,op,level) HOST(name,op,level,int_type,int_type,bool_type)
int main(int argc, char **argv) {
    env_t *env = 0;
    for (int i = 0; i < 256; i++) intern((char[2]){i, 0}); // must be first 256
    for (int i = 0; resv[i]; i++) resv[i] = intern(resv[i]);
    ignore = intern(ignore);
    bool_type = new_type_oper("bool", 0);
    int_type = new_type_oper("int", 0);
    str_type = new_type_oper("string", 0);
    tuple_type = new_type_oper("tuple", 0);
    list_type = new_type_oper("list", 0);
    fun_type = new_type_oper("fun", 0);
    type_t *a = new_type_var();
    IBIN(*,OMUL,8)IBIN(/,ODIV,8)IBIN(rem,OREM,8)IBIN(+,OADD,7)IBIN(-,OSUB,7)
    HOST(:,OCONS,-7,a,new_list_type(a),new_list_type(a))
    ICMP(==,OEQ,6)ICMP(/=,ONE,6)ICMP(<=,OLE,6)ICMP(>=,OGE,6)
    ICMP(<,OLT,6)ICMP(>,OGT,6)HOST(print,OPRN,0,str_type,str_type)
    HOST(equals,OEQUALS,6,str_type,str_type,bool_type)
    HOST(subs,OSUBS,0,int_type,int_type,str_type,str_type)
    HOST(lengths,OLENS,0,str_type,int_type)
    HOST(implode,OIMPLODE,1,new_list_type(str_type),str_type)
    HOST(explode,OEXPLODE,1,str_type,new_list_type(str_type))
    HOST(chr,OCHR,1,int_type,str_type) HOST(ord,OORD,1,str_type,int_type)
    *++ops=(struct op_t){5,intern("and")}, *++ops=(struct op_t){5,intern("or")};
    FILE *file = fopen(argv[1], "rb");
    if (not file) syntax(line, "cannot open file");
    fread(source, 1, sizeof source, file), fclose(file);
    exp_t *e = _exp(); need(TEOF);
    assign(env, e, 0);
    print_type(e->type); printf(" :: ");
    print(eval(env, e), e->type);
}
