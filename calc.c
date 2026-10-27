// Hassan Ahmad 241ADB154
// https://github.com/Hassan-ahmad0/calc-lab-home
// Compile with: gcc -O2 -Wall -Wextra -std=c17 -o calc calc.c -lm
// Resources used: Lab handout and sample tests (calc-tests.zip),
// K&R "The C Programming Language" (recursive descent grammar),
// Linux man pages (strtod, mkdir, readdir, stat), and AI-assisted design log: https://share.gemini.google/z2qwKrvqcbPS

#define STUDENT_NAME "hassan"
#define STUDENT_LASTNAME "ahmad"
#define STUDENT_ID "241ADB154"

// Required to expose POSIX functions (mkdir, stat, realpath) under -std=c17
#define _XOPEN_SOURCE 700

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

// Value type: stores either a 64-bit integer or double-precision float.
// Operations stay in integer mode unless at least one operand is a float.
typedef struct {
    int is_float;
    long long i;
    double f;
} Val;

// Stack item for right-associative '**' evaluation
typedef struct {
    Val v;
    size_t start; // 0-based start index of operand
    size_t op;    // 0-based index of '**' operator
} PowItem;

/* 
 * AI prompt reference: 
 * "How should I structure parse_primary using a Parser struct for cross-line tracking?"
 */
typedef struct {
    char *s;
    size_t len;
    size_t i;     // current 0-based cursor
    size_t err;   // 0-based index of first error
    int depth;    // current parenthesis nesting depth
    PowItem *st;  // dynamic stack for '**' chains
    size_t top, cap;
} Parser;

#define MAX_DEPTH 10000

static int parse_expr(Parser *p, Val *out);

// Only spaces and tabs are valid token separators
static void skip_ws(Parser *p) {
    while (p->s[p->i] == ' ' || p->s[p->i] == '\t') p->i++;
}

static int is_digit(char c) { return c >= '0' && c <= '9'; }

static int fail(Parser *p, size_t at) {
    p->err = at;
    return 0;
}

// End of line is either '\n' or EOF (explicit length check catches embedded '\0' bytes)
static int at_eol(const Parser *p) { return p->i >= p->len || p->s[p->i] == '\n'; }

// O(log exp) integer exponentiation using unsigned math to avoid signed overflow UB.
// Starting result at 1 satisfies x ** 0 == 1 (including 0 ** 0 == 1).
static long long ipow(long long base, long long exp) {
    unsigned long long result = 1, b = (unsigned long long)base;
    unsigned long long e = (unsigned long long)exp;
    while (e > 0) {
        if (e & 1) result *= b;
        b *= b;
        e >>= 1;
    }
    return (long long)result;
}

static double as_double(Val v) { return v.is_float ? v.f : (double)v.i; }

// Evaluates +, -, *, /.
// Division by zero reports the error at rhs_start (start of right operand).
// Float overflow/NaN reports the error at op_pos (the operator).
static int apply_arith(Parser *p, char op, Val a, Val b, size_t op_pos, size_t rhs_start, Val *out) {
    Val r;
    if (!a.is_float && !b.is_float) {
        r.is_float = 0;
        r.f = 0.0;
        // Cast to unsigned long long to prevent signed integer overflow UB
        unsigned long long ua = (unsigned long long)a.i, ub = (unsigned long long)b.i;
        switch (op) {
        case '+': r.i = (long long)(ua + ub); break;
        case '-': r.i = (long long)(ua - ub); break;
        case '*': r.i = (long long)(ua * ub); break;
        default:
            if (b.i == 0) return fail(p, rhs_start);
            r.i = (b.i == -1) ? (long long)(0ULL - ua) : a.i / b.i;
            break;
        }
    } else {
        double x = as_double(a), y = as_double(b), z;
        switch (op) {
        case '+': z = x + y; break;
        case '-': z = x - y; break;
        case '*': z = x * y; break;
        default:
            if (y == 0.0) return fail(p, rhs_start);
            z = x / y;
            break;
        }
        if (!isfinite(z)) return fail(p, op_pos);
        r.is_float = 1;
        r.f = z;
        r.i = 0;
    }
    *out = r;
    return 1;
}

// Evaluates base ** ex.
// Negative integer exponents fail at exp_start; float NaN/Inf fails at op_pos.
static int apply_pow(Parser *p, Val base, Val ex, size_t op_pos, size_t exp_start, Val *out) {
    Val r;
    if (!base.is_float && !ex.is_float) {
        if (ex.i < 0) return fail(p, exp_start);
        r.is_float = 0;
        r.i = ipow(base.i, ex.i);
        r.f = 0.0;
    } else {
        double z = pow(as_double(base), as_double(ex));
        if (!isfinite(z)) return fail(p, op_pos);
        r.is_float = 1;
        r.f = z;
        r.i = 0;
    }
    *out = r;
    return 1;
}

/* 
 * AI prompt reference: 
 * "How can I properly parse numbers and validate floating-point dots while tracking character positions?"
 */
static int parse_primary(Parser *p, Val *out) {
    size_t start = p->i;
    char c = p->s[start];

    if (is_digit(c)) {
        size_t j = start;
        while (is_digit(p->s[j])) j++;
        if (p->s[j] == '.') {
            // Floats require digits on both sides of '.' (rejects "5." at the dot)
            if (!is_digit(p->s[j + 1])) return fail(p, j);
            j++;
            while (is_digit(p->s[j])) j++;
            // Temporarily null-terminate so strtod only parses digits and not 'e'/'E'
            char saved = p->s[j];
            p->s[j] = '\0';
            double d = strtod(p->s + start, NULL);
            p->s[j] = saved;
            if (!isfinite(d)) return fail(p, start);
            out->is_float = 1;
            out->f = d;
            out->i = 0;
        } else {
            unsigned long long v = 0;
            for (size_t k = start; k < j; k++) v = v * 10ULL + (unsigned long long)(p->s[k] - '0');
            out->is_float = 0;
            out->i = (long long)v;
            out->f = 0.0;
        }
        p->i = j;
        return 1;
    }

    if (c == '(') {
        if (p->depth >= MAX_DEPTH) return fail(p, start);
        p->depth++;
        p->i++;
        skip_ws(p);
        if (!parse_expr(p, out)) return 0;
        skip_ws(p);
        if (p->s[p->i] != ')' || p->i >= p->len) return fail(p, p->i);
        p->i++;
        p->depth--;
        return 1;
    }

    // Any other token (unary minus, leading '.', extra ')', EOF) is a syntax error here
    return fail(p, start);
}

static int push_item(Parser *p, Val v, size_t start, size_t op) {
    if (p->top == p->cap) {
        size_t ncap = p->cap ? p->cap * 2 : 64;
        PowItem *n = realloc(p->st, ncap * sizeof *n);
        if (!n) {
            fprintf(stderr, "calc: out of memory\n");
            exit(1);
        }
        p->st = n;
        p->cap = ncap;
    }
    p->st[p->top].v = v;
    p->st[p->top].start = start;
    p->st[p->top].op = op;
    p->top++;
    return 1;
}

// Collects a chain of '**' operands onto a heap stack and folds right-to-left
// so 2 ** 3 ** 2 evaluates as 2 ** (3 ** 2) without risking C call-stack overflow.
static int parse_power(Parser *p, Val *out) {
    size_t base = p->top;
    Val v;
    size_t start = p->i;
    if (!parse_primary(p, &v)) return 0;
    push_item(p, v, start, 0);

    for (;;) {
        skip_ws(p);
        if (!(p->s[p->i] == '*' && p->s[p->i + 1] == '*' && p->i + 1 < p->len)) break;
        size_t op = p->i;
        p->i += 2;
        skip_ws(p);
        start = p->i;
        if (!parse_primary(p, &v)) return 0;
        push_item(p, v, start, op);
    }

    Val acc = p->st[p->top - 1].v;
    for (size_t k = p->top - 1; k > base; k--) {
        Val b = p->st[k - 1].v;
        if (!apply_pow(p, b, acc, p->st[k].op, p->st[k].start, &acc)) return 0;
    }
    p->top = base;
    *out = acc;
    return 1;
}

// Left-associative '*' and '/'
static int parse_term(Parser *p, Val *out) {
    Val l;
    if (!parse_power(p, &l)) return 0;
    for (;;) {
        skip_ws(p);
        char c = p->s[p->i];
        if (c != '*' && c != '/') break;
        size_t op = p->i;
        p->i++;
        skip_ws(p);
        size_t rhs = p->i;
        Val r;
        if (!parse_power(p, &r)) return 0;
        if (!apply_arith(p, c, l, r, op, rhs, &l)) return 0;
    }
    *out = l;
    return 1;
}

/* 
 * AI prompt reference: 
 * "How should I structure parse_expr, parse_term, and parse_power for proper precedence and error positions?"
 */
static int parse_expr(Parser *p, Val *out) {
    Val l;
    if (!parse_term(p, &l)) return 0;
    for (;;) {
        skip_ws(p);
        char c = p->s[p->i];
        if (c != '+' && c != '-') break;
        size_t op = p->i;
        p->i++;
        skip_ws(p);
        size_t rhs = p->i;
        Val r;
        if (!parse_term(p, &r)) return 0;
        if (!apply_arith(p, c, l, r, op, rhs, &l)) return 0;
    }
    *out = l;
    return 1;
}

// Reads entire file into memory in O(N) time using a doubling buffer
static char *read_file(const char *path, size_t *len_out) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "calc: cannot open '%s': %s\n", path, strerror(errno));
        return NULL;
    }
    size_t cap = 1 << 16, len = 0;
    char *buf = malloc(cap + 1);
    if (!buf) {
        fprintf(stderr, "calc: out of memory\n");
        fclose(f);
        return NULL;
    }
    for (;;) {
        size_t n = fread(buf + len, 1, cap - len, f);
        len += n;
        if (len < cap) break;
        cap *= 2;
        char *nb = realloc(buf, cap + 1);
        if (!nb) {
            fprintf(stderr, "calc: out of memory\n");
            free(buf);
            fclose(f);
            return NULL;
        }
        buf = nb;
    }
    if (ferror(f)) {
        fprintf(stderr, "calc: cannot read '%s': %s\n", path, strerror(errno));
        free(buf);
        fclose(f);
        return NULL;
    }
    fclose(f);
    buf[len] = '\0';
    *len_out = len;
    return buf;
}

// Evaluates all lines in the file. Blank lines and '#' comment lines produce no output
// but their characters are still counted in p->i for error position reporting.
static int evaluate(Parser *p, FILE *out) {
    p->i = 0;
    while (p->i < p->len) {
        skip_ws(p);
        if (p->i >= p->len) break;
        char c = p->s[p->i];
        if (c == '\n') { p->i++; continue; }
        if (c == '#') {
            const char *nl = memchr(p->s + p->i, '\n', p->len - p->i);
            p->i = nl ? (size_t)(nl - p->s) + 1 : p->len;
            continue;
        }

        p->top = 0;
        p->depth = 0;
        Val v;
        if (!parse_expr(p, &v)) return 1;
        skip_ws(p);
        // Any leftover characters on the line (like inline comments or extra ')') trigger an error
        if (!at_eol(p)) { p->err = p->i; return 1; }

        if (v.is_float) fprintf(out, "%.15g\n", v.f);
        else fprintf(out, "%lld\n", v.i);
        if (p->i < p->len) p->i++;
    }
    return 0;
}

static int ensure_dir(const char *dir) {
    struct stat st;
    if (stat(dir, &st) == 0) {
        if (S_ISDIR(st.st_mode)) return 1;
        fprintf(stderr, "calc: '%s' exists and is not a folder\n", dir);
        return 0;
    }
    if (mkdir(dir, 0777) != 0 && errno != EEXIST) {
        fprintf(stderr, "calc: cannot create folder '%s': %s\n", dir, strerror(errno));
        return 0;
    }
    return 1;
}

// Extracts base filename without directory path or trailing slashes
static void base_name(const char *path, char *dst, size_t cap) {
    size_t n = strlen(path);
    while (n > 1 && path[n - 1] == '/') n--;
    size_t start = n;
    while (start > 0 && path[start - 1] != '/') start--;
    size_t len = n - start;
    if (len >= cap) len = cap - 1;
    memcpy(dst, path + start, len);
    dst[len] = '\0';
}

/* 
 * AI prompt reference: 
 * "How should I handle command-line arguments, file reading, and the all-or-nothing error policy?"
 */
static int process_file(const char *input, const char *outdir) {
    size_t len;
    char *text = read_file(input, &len);
    if (!text) return 1;

    char base[1024];
    base_name(input, base, sizeof base);
    size_t bl = strlen(base);
    if (bl > 4 && strcmp(base + bl - 4, ".txt") == 0) base[bl - 4] = '\0';

    if (!ensure_dir(outdir)) { free(text); return 1; }

    size_t plen = strlen(outdir) + strlen(base) + 128;
    char *path = malloc(plen);
    if (!path) { fprintf(stderr, "calc: out of memory\n"); free(text); return 1; }
    snprintf(path, plen, "%s/%s_%s_%s_%s.txt", outdir, base, STUDENT_NAME, STUDENT_LASTNAME, STUDENT_ID);

    FILE *out = fopen(path, "wb");
    if (!out) {
        fprintf(stderr, "calc: cannot write '%s': %s\n", path, strerror(errno));
        free(path); free(text);
        return 1;
    }
    static char iobuf[1 << 16];
    setvbuf(out, iobuf, _IOFBF, sizeof iobuf);

    Parser p = {0};
    p.s = text;
    p.len = len;
    int had_error = evaluate(&p, out);
    int rc = 0;

    // If any error occurs in the file, discard partial results and output only ERROR:<pos>
    if (had_error) {
        fclose(out);
        out = fopen(path, "wb");
        if (!out) {
            fprintf(stderr, "calc: cannot write '%s': %s\n", path, strerror(errno));
            rc = 1;
        } else {
            fprintf(out, "ERROR:%zu\n", p.err + 1);
        }
    }
    if (out && fclose(out) != 0) {
        fprintf(stderr, "calc: error writing '%s': %s\n", path, strerror(errno));
        rc = 1;
    }
    free(p.st);
    free(path);
    free(text);
    return rc;
}

static void usage(void) {
    fprintf(stderr, "usage: calc [-d DIR | --dir DIR] [-o OUTDIR | --output-dir OUTDIR] [input.txt]\n");
}

int main(int argc, char **argv) {
    const char *dir = NULL, *outdir = NULL, *input = NULL;

    for (int a = 1; a < argc; a++) {
        const char *arg = argv[a];
        int is_d = strcmp(arg, "-d") == 0 || strcmp(arg, "--dir") == 0;
        int is_o = strcmp(arg, "-o") == 0 || strcmp(arg, "--output-dir") == 0;
        if (is_d || is_o) {
            if (a + 1 >= argc) {
                fprintf(stderr, "calc: option '%s' needs an argument\n", arg);
                usage();
                return 2;
            }
            if (is_d) dir = argv[++a];
            else outdir = argv[++a];
        } else if (arg[0] == '-' && arg[1] != '\0') {
            fprintf(stderr, "calc: unknown option '%s'\n", arg);
            usage();
            return 2;
        } else if (input == NULL) {
            input = arg;
        } else {
            fprintf(stderr, "calc: more than one input file given\n");
            usage();
            return 2;
        }
    }
    if ((dir == NULL) == (input == NULL)) {
        usage();
        return 2;
    }

    char defdir[2048];

    // Single input file mode
    if (input) {
        if (!outdir) {
            char b[1024];
            base_name(input, b, sizeof b);
            size_t bl = strlen(b);
            if (bl > 4 && strcmp(b + bl - 4, ".txt") == 0) b[bl - 4] = '\0';
            snprintf(defdir, sizeof defdir, "%s_%s_%s", b, STUDENT_NAME, STUDENT_ID);
            outdir = defdir;
        }
        return process_file(input, outdir);
    }

    // Directory mode (-d / --dir): process only regular *.txt files directly inside dir
    DIR *d = opendir(dir);
    if (!d) {
        fprintf(stderr, "calc: cannot open folder '%s': %s\n", dir, strerror(errno));
        return 1;
    }
    if (!outdir) {
        char b[1024];
        base_name(dir, b, sizeof b);
        if (strcmp(b, ".") == 0 || strcmp(b, "..") == 0) {
            char *rp = realpath(dir, NULL);
            if (rp) { base_name(rp, b, sizeof b); free(rp); }
        }
        snprintf(defdir, sizeof defdir, "%s_%s_%s", b, STUDENT_NAME, STUDENT_ID);
        outdir = defdir;
    }

    int rc = 0;
    struct dirent *e;
    while ((e = readdir(d)) != NULL) {
        size_t nl = strlen(e->d_name);
        if (nl <= 4 || strcmp(e->d_name + nl - 4, ".txt") != 0) continue;

        size_t fl = strlen(dir) + nl + 2;
        char *full = malloc(fl);
        if (!full) { fprintf(stderr, "calc: out of memory\n"); rc = 1; break; }
        snprintf(full, fl, "%s/%s", dir, e->d_name);

        struct stat st;
        if (stat(full, &st) == 0 && S_ISREG(st.st_mode)) {
            if (process_file(full, outdir) != 0) rc = 1;
        }
        free(full);
    }
    closedir(d);
    return rc;
}