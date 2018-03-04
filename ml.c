#include <ctype.h>
#include <iso646.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef struct value_t value_t;
struct value_t {
    enum { BOOL, INT, STRING, LIST, FUN, HOST } type;
    union { bool b;
            int i;
            uint8_t *s;
            struct list_t *l;
            struct { uint8_t *param; struct exp_t *body; struct env_t *env; } f;
            struct host_t { int op, i, n; struct env_t *env; } h;
    };
};
typedef struct env_t { uint8_t *name; value_t value; struct env_t *tl; } env_t;
typedef struct list_t { value_t hd; struct list_t *tl; } list_t;
typedef struct exp_t exp_t;
struct exp_t {
    enum { ECONST, ECONS, ENAME, EFUN, EAPP, EIF, EMATCH, ELET, ELETREC, } op;
    int line;
    union { int integer;
            uint8_t *string, *name;
            value_t value;
            struct { uint8_t *param; exp_t *body; } fun;
            struct { exp_t *lhs, *rhs; } app, cons, cat;
            struct { exp_t *cond, *t, *f; } cond;
            struct rule_t { exp_t *lhs, *rhs; struct rule_t *next; } rule;
            struct { exp_t *cond; struct rule_t *rule; } match;
            struct { uint8_t *name; exp_t *value, *body; } let;
            struct dec_t { uint8_t *name; exp_t *value; struct dec_t *tl; } dec;
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
            "let", "rec", "in", "and", "or", "__op", NULL};
struct op_t { int level; uint8_t *name; } _ops[256], *ops=_ops-1, *last_op;
char    *interns[65536];
int     ninterns;
value_t nilv={LIST}, falsev={BOOL}, truev={BOOL,.b=true};
#define new(type, ...) copy(sizeof(type), &(type){__VA_ARGS__})
#define exp(head, ...) new(exp_t, head, line, __VA_ARGS__)
void *copy(size_t size, void *proto) {
    return memmove(malloc(size), proto, size);
}
void panic(uint8_t *msg, ...);
value_t newi(int x) { return (value_t){INT, .i=x}; }
value_t news(uint8_t *x) { return (value_t){STRING, .s=x}; }
value_t newl(list_t *x) { return (value_t){LIST, .l=x}; }
value_t newf(uint8_t *param, exp_t *body, env_t *env) {
    return (value_t){FUN, .f={param, body, env}};
}
value_t newh(int op, int n) {
    return (value_t){HOST, .h={op, 0, n, 0}};
}
list_t *cons(value_t hd, list_t *tl) { return new(list_t, hd, tl); }
list_t *concat(list_t *a, list_t *b) {
    if (not a) return b;
    return cons(a->hd, concat(a->tl, b));
}
void print(value_t x) {
    switch (x.type) {
    case BOOL:      printf(x.b ? "true" : "false"); break;
    case INT:       printf("%d", x.i); break;
    case STRING:    printf("%s", x.s); break;
    case LIST:      printf("[");
                    for (list_t *i = x.l; i; i = i->tl)
                        print(i->hd),
                        printf(i->tl ? ", " : "");
                    printf("]"); break;
    case FUN:       printf("(fun %s -> ...)", x.f.param); break;
    case HOST:      printf("host_%02d:%d/%d", x.h.op, x.h.i, x.h.n); break;
    }
}
void echo(value_t x) { print(x); puts(""); }
void panic(uint8_t *msg, ...) {
    printf("PANIC - ");
    va_list ap; va_start(ap, msg);
    for ( ; *msg; msg++)
        if (*msg != '%') putchar(*msg);
        else switch (*++msg) {
        case 'd':   printf("%d", va_arg(ap, int)); break;
        case 's':   printf("%s", va_arg(ap, char*)); break;
        case 'v':   print(va_arg(ap, value_t)); break;
        }
    puts(""); exit(2);
}
void syntax(int line, uint8_t *msg, ...) {
    va_list ap; va_start(ap, msg);
    printf("error %d: ", line);
    vprintf(msg, ap), puts(".");
    exit(1);
}
uint8_t *intern(uint8_t *txt) {
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
    uint8_t *p, *t=tbuf;
    if (p = strchr(pun, *src)) return src++, token = TLP + p - pun;
    if (isdigit(src[*src == '-']))
        return tint = strtoul(src, &src, 10), token = TINT;
    if (*src == '"')
        for (char quote = *src++; ; src++)
            if (*src == quote)
                return src++, *t=0, tstr=intern(tbuf), token=TSTR;
            else if (not *src) syntax(line, "unclosed string");
            else if (*src == '\\') {
                uint8_t *p = strchr("a\ab\be\033n\nr\rt\t", *++src);
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
exp_t *_exp();
struct op_t *operator(int level, uint8_t *name) {
    for (struct op_t *i = ops; i >= _ops; i--)
        if (i->name == name and (not level or abs(i->level) == level))
            return last_op=i;
    return 0;
}
exp_t *prefixed(int t) { need(t); return _exp(); }
exp_t *list() {
    if (peek(TRB)) return exp(ECONST, .value=nilv);
    exp_t *hd = _exp();
    exp_t *tl = want(TCOMMA) ? list() : exp(ECONST, .value=nilv);
    return exp(ECONS, .cons={hd, tl});
}
exp_t *function() {
    if (want(TNAME)) {
        uint8_t *name = tstr;
        return exp(EFUN, .fun={name, function()});
    } else { if (not want(TEQ)) need(TARROW); return _exp(); }
}
exp_t *atom(bool required, bool is_pattern) {
    exp_t *e;
    switch (next()) {
    case TFALSE:    return exp(ECONST, .value=falsev);
    case TTRUE:     return exp(ECONST, .value=truev);
    case TINT:      return exp(ECONST, .value=newi(tint));
    case TSTR:      return exp(ECONST, .value=news(tstr));
    case TLP:       e = list(); need(TRP);
                    return e->op == ECONS and e->cons.rhs->op != ECONS
                        ? e->cons.lhs : e;
    case TLB:       e = list(); need(TRB); return e;
    case TNAME:     if (not required and operator(0, tstr)) goto abort;
                    return exp(ENAME, .name=tstr);
    case TFUN:      if (is_pattern) goto abort; return function();
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
            exp_t *t = is_and ? infexp(level) : exp(ECONST, .value=truev);
            exp_t *f = is_and ? exp(ECONST, .value=falsev) : infexp(level);
            e = exp(EIF, .cond={e, t, f});
        } else {
            exp_t *lhs = exp(EAPP, .app={exp(ENAME, .name=tstr), e});
            exp_t *rhs = infexp(last_op->level < 0 ? level : level + 1);
            e = exp(EAPP, .app={lhs, rhs});
        }
    }
    return e;
}
exp_t *pattern() {
    exp_t *e = atom(true, true);
    if (peek(TNAME) and not strcmp(tstr, ":") and want(TNAME))
        return exp(ECONS, .cons={e, pattern()});
    return e;
}
struct rule_t *_rules() {
    if (not want(TBAR)) return 0;
    exp_t *lhs = pattern();
    exp_t *rhs = prefixed(TARROW);
    struct rule_t *next = _rules();
    return new(struct rule_t, lhs, rhs, next);
}
struct dec_t *_decs() {
    uint8_t *name = (need(TNAME), tstr);
    exp_t *value = peek(TNAME) ? function() : prefixed(TEQ);
    struct dec_t *tl = want(TSEMI) and not peek(TIN) ? _decs() : 0;
    return new(struct dec_t, name, value, tl);
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
        uint8_t *name = tstr;
        exp_t *value = peek(TNAME) ? function() : prefixed(TEQ);
        exp_t *body = want(TLET) ? _let() : prefixed(TIN);
        return exp(ELET, .let={name, value, body});
    } else {
        exp_t *pat = pattern();
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
value_t lookup(exp_t *e, env_t *env, uint8_t *name) {
    if (not env) panic("line %d: %s not defined", e->line, name);
    return env->name == name ? env->value : lookup(e, env->tl, name);
}
value_t set(env_t *env, uint8_t *name, value_t value) {
    if (not env) panic("%s not defined", name);
    return env->name == name ? (env->value = value) : set(env->tl, name, value);
}
env_t *define(env_t *env, uint8_t *name, value_t value) {
    return new(env_t, name, value, env);
}
bool equal(value_t a, value_t b) {
    if (a.type != b.type) panic("CANNOT COMPARE `%v` and `%v`", a, b);
    switch (a.type) {
    case BOOL:      return a.b == b.b;
    case INT:       return a.i == b.i;
    case STRING:    return a.s == b.s or not strcmp(a.s, b.s);
    case LIST:      return  a.l == NULL and b.l == NULL or
                            a.l and b.l and
                            equal(a.l->hd, b.l->hd) and
                            equal(newl(a.l->tl), newl(b.l->tl));
    default:        return panic("CANNOT COMPARE TYPE `%v`", a), false;
    }
}
enum { OMUL=1, ODIV, OREM, OADD, OSUB, OLT, OGT, OLE, OGE, OEQ, ONE, OCONS,
    OORD, OCHR, OSUBS, OLENS, OEXPLODE, OIMPLODE, OPRINT, OREADF, OWRITEF, };
value_t asx(value_t x, uint8_t *what, int type, uint8_t *types) {
    if (x.type != type) panic("%s SHOULD BE %s NOT `%v`", what, types, x);
    return x;
}
int asi(value_t x, uint8_t *what) { return asx(x, what, INT, "INT").i; }
list_t *asl(value_t x, uint8_t *what) { return asx(x, what, LIST, "LIST").l; }
uint8_t *ass(value_t x, uint8_t *what) { return asx(x, what, STRING, "STRING").s; }
value_t host(struct host_t h, value_t x) {
    value_t w = h.env ? h.env->value : nilv;
    value_t v = h.env and h.env->tl ? h.env->tl->value : nilv;
    FILE    *file;
    switch (h.op) {
    case OMUL:  return newi(asi(w, "LHS") * asi(x, "RHS"));
    case ODIV:  if (not asi(x, "RHS")) panic("DIVISION BY ZERO");
                return newi(asi(w, "LHS") / asi(x, "RHS"));
    case OREM:  if (not asi(x, "RHS")) panic("DIVISION BY ZERO");
                return newi(asi(w, "LHS") % asi(x, "RHS"));
    case OADD:  return newi(asi(w, "LHS") + asi(x, "RHS"));
    case OSUB:  return newi(asi(w, "LHS") - asi(x, "RHS"));
    case OLT:   return asi(w, "LHS") < asi(x, "RHS") ? truev : falsev;
    case OGT:   return asi(w, "LHS") > asi(x, "RHS") ? truev : falsev;
    case OLE:   return asi(w, "LHS") <= asi(x, "RHS") ? truev : falsev;
    case OGE:   return asi(w, "LHS") >= asi(x, "RHS") ? truev : falsev;
    case OEQ:   return equal(w, x) ? truev : falsev;
    case ONE:   return not equal(w, x) ? truev : falsev;
    case OCONS: return newl(cons(w, asl(x, "RHS")));
    case OORD:  return newi(ass(x, "ORD")[0]);
    case OCHR:  {   int i = asi(x, "CHR");
                    if (i < 0 or i > 255) panic("CHR %d NOT BETWEEN 0-255", i);
                    return news(interns[i]); }
    case OSUBS: {   int n = strlen(ass(x, "STRING"));
                    int i = asi(v, "I"), j = asi(w, "J");
                    i += i < 0 ? n + 1 : 0; j += j < 0 ? n + 1: 0;
                    if (i < 0 or i > j or j > n)
                        panic("BAD INDEX %d:%d/%d", i, j, n);
                    if (i == j + 1) return news(interns[ass(x,0)[i]]);
                    char *txt = memmove(malloc(j - i + 1), ass(x,0) + i, j - i);
                    return txt[j - i] = 0, news(txt); }
    case OLENS: return newi(strlen(ass(x, "STRING")));
    case OEXPLODE:{ char *txt = ass(x, "STRING");
                    list_t *tl = 0;
                    for (int i = strlen(txt) - 1; i >= 0; i--)
                        tl = cons(news(interns[txt[i]]), tl);
                    return newl(tl); }
    case OIMPLODE:{ char *txt = 0;
                    int total = 0, n;
                    for (list_t *i = asl(x, "LIST"); i; i = i->tl)
                        n = strlen(ass(i->hd, "PART")),
                        txt = realloc(txt, (total += n) + 1),
                        memmove(&txt[total - n], ass(i->hd,0), n);
                    return txt[total] = 0, news(txt); }
    case OPRINT: return print(x), x;
    case OREADF: {  FILE *file = fopen(ass(x, "FILENAME"), "rb");
                    if (not file) panic("CANNOT OPEN FILE '%v'", x);
                    size_t len = (fseek(file, 0, SEEK_END), ftell(file));
                    uint8_t *text = malloc(len + 1);
                    rewind(file), text[fread(text, 1, len, file)] = 0;
                    return fclose(file), news(text); }
    case OWRITEF: { FILE *file = fopen(ass(w, "FILENAME"), "wb");
                    if (not file) panic("CANNOT OPEN FILE '%v'", x);
                    fwrite(ass(x, "DATA"), 1, strlen(ass(x,0)), file);
                    return fclose(file), x; }
    default:    return panic("HOST(%d)", h.op), nilv;
    }
}
env_t *match(env_t *env, exp_t *e, value_t x) {
    switch (e->op) {
    case ECONST: return x.type == e->value.type and equal(e->value, x) ? env: 0;
    case ECONS: return x.type == LIST and
                        (env = match(env, e->cons.lhs, x.l->hd)) and
                        (env = match(env, e->cons.rhs, newl(x.l->tl)))
                        ? env : 0;
    case ENAME: return e->name == ignore ? env : define(env, e->name, x);
    default:    return panic("MATCH(%d)", e->op), 0;
    }
}
value_t eval(env_t *env, exp_t *e) {
    value_t x, y;
    tail:
    switch (e->op) {
    case ECONST:    return e->value;
    case ECONS:     x = eval(env, e->cons.lhs);
                    y = eval(env, e->cons.rhs);
                    return newl(cons(x, asl(y, "RHS")));
    case ENAME:     return lookup(e, env, e->name);
    case EFUN:      return newf(e->fun.param, e->fun.body, env);
    case EAPP:      x = eval(env, e->app.lhs);
                    y = eval(env, e->app.rhs);
                    if (x.type == FUN) {
                        env = define(x.f.env, x.f.param, y);
                        e = x.f.body; goto tail;
                    } else if (x.type == HOST and x.h.i == x.h.n - 1)
                        return host(x.h, y);
                    else if (x.type == HOST)
                        return x.h.i++, x.h.env = define(x.h.env, 0, y), x;
                    else { panic("CANNOT CALL `%v`", x); return nilv; }
    case EIF:       x = eval(env, e->cond.cond);
                    if (x.type != BOOL) panic("CONDITION NOT BOOLEAN `%v`", x);
                    e = x.b ? e->cond.t : e->cond.f; goto tail;
    case EMATCH:    x = eval(env, e->match.cond);
                    env_t *new_env;
                    for (struct rule_t *i = e->match.rule; i; i = i->next)
                        if (new_env = match(env, i->lhs, x))
                            { e = i->rhs; env = new_env; goto tail; }
                    return panic("line %d: CRASH ON `%v`", e->line, x), nilv;
    case ELET:      x = eval(env, e->let.value);
                    env = define(env, e->let.name, x);
                    e = e->let.body; goto tail;
    case ELETREC:   for (struct dec_t *i = e->letrec.decs; i; i = i->tl)
                        env = define(env, i->name, nilv);
                    for (struct dec_t *i = e->letrec.decs; i; i = i->tl)
                        set(env, i->name, eval(env, i->value));
                    e = e->letrec.body; goto tail;
    default:        return panic("EVAL(%d)", e->op), nilv;
    }
}
struct def_t { uint8_t *name; int op, n, level; } hosts[] = {
    {"*",OMUL,2,8},{"/",ODIV,2,8},{"rem",OREM,2,8},{"+",OADD,2,7},
    {"-",OSUB,2,7},{":",OCONS,2,-7},{"<",OLT,2,6},{">",OGT,2,6},{"<=",OLE,2,6},
    {">=",OGE,2,6},{"==",OEQ,2,6},{"/=",ONE,2,6},{"and",0,2,-5},{"or",0,2,-5},
    {"ord",OORD,1,0},{"chr",OCHR,1,0},{"subs",OSUBS,3,0},{"lens",OLENS,1,0},
    {"explode",OEXPLODE,1,0},{"implode",OIMPLODE,1,0},
    {"print",OPRINT,1,0},{"read_file",OREADF,1,0},{"write_file",OWRITEF,2,0}, {0}};
int main(int argc, char **argv) {
    env_t *env = 0;
    for (int i = 0; i < 256; i++) intern((char[2]){i, 0}); // must be first 256
    for (int i = 0; resv[i]; i++) resv[i] = intern(resv[i]);
    ignore = intern(ignore);
    for (struct def_t *i = hosts; i->name; i++)
        env = define(env, intern(i->name), newh(i->op, i->n)),
        i->level ? (*++ops = (struct op_t){i->level, intern(i->name)}, 0) : 0;
    FILE *file = fopen(argv[1], "rb");
    if (not file) syntax(line, "cannot open file");
    fread(source, 1, sizeof source, file), fclose(file);
    exp_t *e = _exp(); need(TEOF);
    eval(env, e);
}