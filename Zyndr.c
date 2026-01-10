
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdbool.h>
#include <ctype.h>

#define STRDUP(s) (strdup(s))
__attribute__((noreturn))
static void die(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fprintf(stderr, "\n");
    exit(1);
}

typedef struct { char *data; size_t len, cap; } buf;
static void binit(buf *b){b->cap=4096;b->len=0;b->data=malloc(b->cap);b->data[0]=0;}
static void bput(buf *b, const char *s){size_t n=strlen(s); if(b->len+n+1> b->cap){b->cap=(b->len+n+1)*2; b->data=realloc(b->data,b->cap);} memcpy(b->data+b->len,s,n); b->len+=n; b->data[b->len]=0;}
static void bprintf(buf *b, const char *fmt, ...){ char tmp[1024]; va_list ap; va_start(ap,fmt); vsnprintf(tmp,sizeof(tmp),fmt,ap); va_end(ap); bput(b,tmp);}

typedef struct FileNode { char *path; struct FileNode *next; } FileNode;
static FileNode *loaded_files = NULL;
static bool file_loaded(const char *path){
    for(FileNode *n=loaded_files;n;n=n->next) if(strcmp(n->path,path)==0) return true;
    return false;
}
static void mark_loaded(const char *path){
    FileNode *n = malloc(sizeof(*n)); n->path = STRDUP(path); n->next = loaded_files; loaded_files = n;
}
static char *read_file(const char *path){
    FILE *f = fopen(path,"rb"); if(!f) return NULL;
    fseek(f,0,SEEK_END); long s = ftell(f); fseek(f,0,SEEK_SET);
    char *buf = malloc(s+1); if(fread(buf,1,s,f) != (size_t)s){ free(buf); fclose(f); return NULL; }
    buf[s]=0; fclose(f); return buf;
}

typedef enum {
    TK_EOF=0, TK_IDENT, TK_NUMBER, TK_STRING,
    TK_SEMI, TK_COMMA, TK_LP, TK_RP, TK_LC, TK_RC,
    TK_LT, TK_GT,
    TK_PLUS, TK_MINUS, TK_ASTER, TK_SLASH, TK_PERCENT,
    TK_AND, TK_OR, TK_XOR, TK_SHL, TK_SHR,
    TK_ASSIGN, TK_PLUS_EQ, TK_MINUS_EQ, TK_MUL_EQ, TK_DIV_EQ, TK_MOD_EQ,
    TK_AND_EQ, TK_OR_EQ, TK_XOR_EQ, TK_SHL_EQ, TK_SHR_EQ,
    TK_EQ, TK_NEQ, TK_LE, TK_GE,
    TK_KEYWORD_FN, TK_KEYWORD_EXTERN, TK_KEYWORD_PIN, TK_KEYWORD_IMPORT,
    TK_KEYWORD_IF, TK_KEYWORD_ELSE, TK_KEYWORD_WHILE, TK_KEYWORD_RETURN
} TokenKind;

typedef struct { TokenKind kind; char *str; int line; } Token;
typedef struct { const char *s; int pos; int line; } Lexer;

static void lex_skip_space(Lexer *L){ while(L->s[L->pos] && (L->s[L->pos]==' '||L->s[L->pos]=='\t'||L->s[L->pos]=='\r'||L->s[L->pos]=='\n')){ if(L->s[L->pos]=='\n') L->line++; L->pos++; } }

static Token lex_next(Lexer *L){
    lex_skip_space(L);
    Token t = {TK_EOF, NULL, L->line};
    char c = L->s[L->pos];
    if(!c){ t.kind = TK_EOF; return t; }
    if(isalpha(c) || c=='_' ){
        int st = L->pos;
        while(isalnum(L->s[L->pos]) || L->s[L->pos]=='_' ) L->pos++;
        int n = L->pos - st;
        char *id = malloc(n+1); memcpy(id, L->s+st, n); id[n]=0;
        t.str = id;
        if(strcmp(id,"fn")==0) t.kind = TK_KEYWORD_FN;
        else if(strcmp(id,"extern")==0) t.kind = TK_KEYWORD_EXTERN;
        else if(strcmp(id,"pin")==0) t.kind = TK_KEYWORD_PIN;
        else if(strcmp(id,"import")==0) t.kind = TK_KEYWORD_IMPORT;
        else if(strcmp(id,"if")==0) t.kind = TK_KEYWORD_IF;
        else if(strcmp(id,"else")==0) t.kind = TK_KEYWORD_ELSE;
        else if(strcmp(id,"while")==0) t.kind = TK_KEYWORD_WHILE;
        else if(strcmp(id,"return")==0) t.kind = TK_KEYWORD_RETURN;
        else t.kind = TK_IDENT;
        return t;
    }
    if(isdigit(c) || (c=='.' && isdigit(L->s[L->pos+1]))){
        int st = L->pos; bool seen_dot=false;
        if(L->s[L->pos]=='.') { seen_dot = true; L->pos++; }
        while(isdigit(L->s[L->pos]) || (!seen_dot && L->s[L->pos]=='.')){ if(L->s[L->pos]=='.') seen_dot=true; L->pos++; }
        int n = L->pos - st; char *num = malloc(n+1); memcpy(num,L->s+st,n); num[n]=0;
        t.kind = TK_NUMBER; t.str = num; return t;
    }
    if(c=='"'){
        L->pos++;
        int st = L->pos;
        while(L->s[L->pos] && L->s[L->pos] != '"'){ if(L->s[L->pos]=='\\') L->pos+=2; else L->pos++; }
        if(!L->s[L->pos]) die("Unterminated string at line %d", L->line);
        int n = L->pos - st; char *str = malloc(n+1); memcpy(str,L->s+st,n); str[n]=0;
        L->pos++; t.kind = TK_STRING; t.str = str; return t;
    }
    if(L->s[L->pos]=='<' && L->s[L->pos+1]=='<'){ L->pos+=2; if(L->s[L->pos]=='='){ L->pos++; t.kind=TK_SHL_EQ; } else t.kind=TK_SHL; return t;}
    if(L->s[L->pos]=='>' && L->s[L->pos+1]=='>'){ L->pos+=2; if(L->s[L->pos]=='='){ L->pos++; t.kind=TK_SHR_EQ; } else t.kind=TK_SHR; return t;}
    if(L->s[L->pos]=='<' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_LE; return t;}
    if(L->s[L->pos]=='>' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_GE; return t;}
    if(L->s[L->pos]=='=' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_EQ; return t;}
    if(L->s[L->pos]=='!' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_NEQ; return t;}
    if(L->s[L->pos]=='+' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_PLUS_EQ; return t;}
    if(L->s[L->pos]=='-' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_MINUS_EQ; return t;}
    if(L->s[L->pos]=='*' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_MUL_EQ; return t;}
    if(L->s[L->pos]=='/' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_DIV_EQ; return t;}
    if(L->s[L->pos]=='%' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_MOD_EQ; return t;}
    if(L->s[L->pos]=='&' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_AND_EQ; return t;}
    if(L->s[L->pos]=='|' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_OR_EQ; return t;}
    if(L->s[L->pos]=='^' && L->s[L->pos+1]=='='){ L->pos+=2; t.kind = TK_XOR_EQ; return t;}
    L->pos++; switch(c){
        case ';': t.kind = TK_SEMI; return t;
        case ',': t.kind = TK_COMMA; return t;
        case '(' : t.kind = TK_LP; return t;
        case ')' : t.kind = TK_RP; return t;
        case '{' : t.kind = TK_LC; return t;
        case '}' : t.kind = TK_RC; return t;
        case '<' : t.kind = TK_LT; return t;
        case '>' : t.kind = TK_GT; return t;
        case '+' : t.kind = TK_PLUS; return t;
        case '-' : t.kind = TK_MINUS; return t;
        case '*' : t.kind = TK_ASTER; return t;
        case '/' : t.kind = TK_SLASH; return t;
        case '%' : t.kind = TK_PERCENT; return t;
        case '&' : t.kind = TK_AND; return t;
        case '|' : t.kind = TK_OR; return t;
        case '^' : t.kind = TK_XOR; return t;
        case '=' : t.kind = TK_ASSIGN; return t;
        default: die("Unknown character '%c' at line %d", c, L->line);
    }
    return t;
}

typedef enum { TY_I8, TY_I16, TY_I32, TY_I64, TY_U8, TY_U16, TY_U32, TY_U64, TY_FLOAT, TY_FLOAT64, TY_STRING, TY_VOID, TY_BOOL } TypeKind;
static const char *tyname(TypeKind k){
    switch(k){
        case TY_I8: return "i8";
        case TY_I16: return "i16";
        case TY_I32: return "i32";
        case TY_I64: return "i64";
        case TY_U8: return "i8";
        case TY_U16: return "i16";
        case TY_U32: return "i32";
        case TY_U64: return "i64";
        case TY_FLOAT: return "float";
        case TY_FLOAT64: return "double";
        case TY_STRING: return "i8*";
        case TY_VOID: return "void";
        case TY_BOOL: return "i1";
    }
    return "i32";
}
static TypeKind parse_type_name(const char *s){
    if(strcmp(s,"int")==0) return TY_I32;
    if(strcmp(s,"int8")==0) return TY_I8;
    if(strcmp(s,"int16")==0) return TY_I16;
    if(strcmp(s,"int32")==0) return TY_I32;
    if(strcmp(s,"int64")==0) return TY_I64;
    if(strcmp(s,"i8")==0) return TY_I8;
    if(strcmp(s,"i16")==0) return TY_I16;
    if(strcmp(s,"i32")==0) return TY_I32;
    if(strcmp(s,"i64")==0) return TY_I64;
    if(strcmp(s,"uint")==0) return TY_U32;
    if(strcmp(s,"uint8")==0) return TY_U8;
    if(strcmp(s,"uint16")==0) return TY_U16;
    if(strcmp(s,"uint32")==0) return TY_U32;
    if(strcmp(s,"uint64")==0) return TY_U64;
    if(strcmp(s,"u8")==0) return TY_U8;
    if(strcmp(s,"u16")==0) return TY_U16;
    if(strcmp(s,"u32")==0) return TY_U32;
    if(strcmp(s,"u64")==0) return TY_U64;
    if(strcmp(s,"float")==0) return TY_FLOAT;
    if(strcmp(s,"float64")==0) return TY_FLOAT64;
    if(strcmp(s,"double")==0) return TY_FLOAT64;
    if(strcmp(s,"string")==0) return TY_STRING;
    if(strcmp(s,"void")==0 || strcmp(s,"null")==0) return TY_VOID;
    if(strcmp(s,"bool")==0) return TY_BOOL;
    die("Unknown type '%s'", s); return TY_I32;
}
static bool try_parse_type_name(const char *s, TypeKind *out){
    if(!s) return false;
    if(strcmp(s,"int")==0){ *out = TY_I32; return true; }
    if(strcmp(s,"int8")==0){ *out = TY_I8; return true; }
    if(strcmp(s,"int16")==0){ *out = TY_I16; return true; }
    if(strcmp(s,"int32")==0){ *out = TY_I32; return true; }
    if(strcmp(s,"int64")==0){ *out = TY_I64; return true; }
    if(strcmp(s,"i8")==0){ *out = TY_I8; return true; }
    if(strcmp(s,"i16")==0){ *out = TY_I16; return true; }
    if(strcmp(s,"i32")==0){ *out = TY_I32; return true; }
    if(strcmp(s,"i64")==0){ *out = TY_I64; return true; }
    if(strcmp(s,"uint")==0){ *out = TY_U32; return true; }
    if(strcmp(s,"uint8")==0){ *out = TY_U8; return true; }
    if(strcmp(s,"uint16")==0){ *out = TY_U16; return true; }
    if(strcmp(s,"uint32")==0){ *out = TY_U32; return true; }
    if(strcmp(s,"uint64")==0){ *out = TY_U64; return true; }
    if(strcmp(s,"u8")==0){ *out = TY_U8; return true; }
    if(strcmp(s,"u16")==0){ *out = TY_U16; return true; }
    if(strcmp(s,"u32")==0){ *out = TY_U32; return true; }
    if(strcmp(s,"u64")==0){ *out = TY_U64; return true; }
    if(strcmp(s,"float")==0){ *out = TY_FLOAT; return true; }
    if(strcmp(s,"float64")==0){ *out = TY_FLOAT64; return true; }
    if(strcmp(s,"double")==0){ *out = TY_FLOAT64; return true; }
    if(strcmp(s,"string")==0){ *out = TY_STRING; return true; }
    if(strcmp(s,"void")==0 || strcmp(s,"null")==0){ *out = TY_VOID; return true; }
    if(strcmp(s,"bool")==0){ *out = TY_BOOL; return true; }
    return false;
}

typedef enum {
    ND_FN, ND_EXTERN, ND_GLOBAL, ND_BLOCK, ND_VARDECL,
    ND_RETURN, ND_IF, ND_WHILE, ND_EXPR, ND_CALL,
    ND_ASSIGN, ND_BINARY, ND_UNARY, ND_LITERAL, ND_IDENT
} NodeKind;

typedef struct Node Node;
typedef struct Var { char *name; TypeKind ty; bool is_global; char *llvm_name; Node *init; struct Var *next; } Var;

struct Node {
    NodeKind kind;
    TypeKind ty;
    int line;
    char *name;
    Var *params;
    Node *body;
    Var *gvar;
    Node *stmts;
    Node *next;
    Node *ret_expr;
    Node *cond;
    Node *then_block;
    Node *else_block;
    Node *while_body;
    char *vname;
    char *sval;
    Node *lhs;
    Node *rhs;
    Node *init;
    int op;
};

static Node *node_alloc(NodeKind k){ Node *n = calloc(1,sizeof(Node)); n->kind=k; return n; }
static Var *var_alloc(const char *name, TypeKind ty){ Var *v = calloc(1,sizeof(Var)); v->name = STRDUP(name); v->ty = ty; v->is_global = false; return v; }

typedef struct { Token *tokens; int idx, cap; int tokcount; } Parser;
static Parser P;
static Token peek(){ if(P.idx < P.tokcount) return P.tokens[P.idx]; Token t={TK_EOF,NULL,0}; return t;}
static Token nexttok(){ Token t = peek(); if(P.idx < P.tokcount) P.idx++; return t;}
static bool tok_is(TokenKind k){ return peek().kind == k; }
static bool tok_accept(TokenKind k){ if(peek().kind==k){ nexttok(); return true;} return false; }
static void tok_expect(TokenKind k){ if(peek().kind!=k) die("Expected token %d but got %d at line %d", k, peek().kind, peek().line); nexttok(); }

enum {
    OP_ADD=1, OP_SUB, OP_MUL, OP_DIV, OP_MOD,
    OP_BAND, OP_BOR, OP_BXOR, OP_SHL, OP_SHR,
    OP_ASSIGN, OP_PLUS_EQ, OP_MINUS_EQ, OP_MUL_EQ, OP_DIV_EQ, OP_MOD_EQ,
    OP_AND_EQ, OP_OR_EQ, OP_XOR_EQ, OP_SHL_EQ, OP_SHR_EQ,
    OP_EQ, OP_NE, OP_LT, OP_LE, OP_GT, OP_GE
};

static Node *parse_expression(int rbp);

static Node *make_literal_from_token(Token t){
    Node *n = node_alloc(ND_LITERAL);
    n->sval = t.str ? STRDUP(t.str) : NULL;
    n->line = t.line;
    return n;
}

static Node *parse_primary(){
    Token t = peek();
    if(t.kind == TK_IDENT){
        nexttok();
        if(tok_accept(TK_LP)){
            Node *n = node_alloc(ND_CALL);
            n->name = STRDUP(t.str);
            Node *first = NULL, *last = NULL;
            if(!tok_is(TK_RP)){
                while(1){
                    Node *arg = parse_expression(0);
                    if(!first) first = last = arg; else { last->next = arg; last = arg; }
                    if(tok_accept(TK_COMMA)) continue;
                    break;
                }
            }
            tok_expect(TK_RP);
            n->body = first;
            return n;
        } else {
            Node *n = node_alloc(ND_IDENT);
            n->sval = STRDUP(t.str);
            return n;
        }
    }
    if(t.kind == TK_NUMBER){
        nexttok();
        return make_literal_from_token(t);
    }
    if(t.kind == TK_STRING){
        nexttok();
        Node *n = node_alloc(ND_LITERAL);
        n->sval = STRDUP(t.str);
        return n;
    }
    if(tok_accept(TK_LP)){
        Node *n = parse_expression(0);
        tok_expect(TK_RP);
        return n;
    }
    die("Unexpected token in primary at line %d", t.line);
    return NULL;
}

static int lbp_of(TokenKind k){
    switch(k){
        case TK_ASSIGN: return 10;
        case TK_PLUS_EQ: case TK_MINUS_EQ: case TK_MUL_EQ: case TK_DIV_EQ: case TK_MOD_EQ:
        case TK_AND_EQ: case TK_OR_EQ: case TK_XOR_EQ: case TK_SHL_EQ: case TK_SHR_EQ: return 10;
        case TK_OR: return 20;
        case TK_XOR: return 30;
        case TK_AND: return 40;
        case TK_SHL: case TK_SHR: return 50;
        case TK_PLUS: case TK_MINUS: return 60;
        case TK_ASTER: case TK_SLASH: case TK_PERCENT: return 70;
        case TK_EQ: case TK_NEQ: case TK_LE: case TK_GE: case TK_LT: case TK_GT: return 15;
        default: return 0;
    }
}

static Node *parse_expression(int rbp){
    Token t = nexttok();
    Node *left = NULL;
    if(t.kind == TK_MINUS){
        Node *r = parse_expression(100);
        Node *n = node_alloc(ND_UNARY); n->op='-'; n->rhs = r;
        left = n;
    } else if(t.kind == TK_PLUS){
        Node *r = parse_expression(100);
        left = r;
    } else {
        P.idx--;
        left = parse_primary();
    }
    while(1){
        Token tk = peek();
        int lbp = lbp_of(tk.kind);
        if(lbp <= rbp) break;
        nexttok();
        Node *n = node_alloc(ND_BINARY);
        n->lhs = left;
        switch(tk.kind){
            case TK_PLUS: n->op = OP_ADD; break;
            case TK_MINUS: n->op = OP_SUB; break;
            case TK_ASTER: n->op = OP_MUL; break;
            case TK_SLASH: n->op = OP_DIV; break;
            case TK_PERCENT: n->op = OP_MOD; break;
            case TK_AND: n->op = OP_BAND; break;
            case TK_OR: n->op = OP_BOR; break;
            case TK_XOR: n->op = OP_BXOR; break;
            case TK_SHL: n->op = OP_SHL; break;
            case TK_SHR: n->op = OP_SHR; break;
            case TK_ASSIGN: n->op = OP_ASSIGN; break;
            case TK_PLUS_EQ: n->op = OP_PLUS_EQ; break;
            case TK_MINUS_EQ: n->op = OP_MINUS_EQ; break;
            case TK_MUL_EQ: n->op = OP_MUL_EQ; break;
            case TK_DIV_EQ: n->op = OP_DIV_EQ; break;
            case TK_MOD_EQ: n->op = OP_MOD_EQ; break;
            case TK_AND_EQ: n->op = OP_AND_EQ; break;
            case TK_OR_EQ: n->op = OP_OR_EQ; break;
            case TK_XOR_EQ: n->op = OP_XOR_EQ; break;
            case TK_SHL_EQ: n->op = OP_SHL_EQ; break;
            case TK_SHR_EQ: n->op = OP_SHR_EQ; break;
            case TK_EQ: n->op = OP_EQ; break;
            case TK_NEQ: n->op = OP_NE; break;
            case TK_LE: n->op = OP_LE; break;
            case TK_GE: n->op = OP_GE; break;
            case TK_LT: n->op = OP_LT; break;
            case TK_GT: n->op = OP_GT; break;
            default: die("Unhandled operator token %d at line %d", tk.kind, tk.line);
        }
        int nbp = lbp;
        if(n->op==OP_ASSIGN || (n->op>=OP_PLUS_EQ && n->op<=OP_SHR_EQ)) nbp = lbp - 1;
        n->rhs = parse_expression(nbp);
        left = n;
    }
    return left;
}

static Node *parse_statement();
static Node *parse_top();

static Var *parse_param(){
    Token id = peek(); if(id.kind != TK_IDENT) die("Expected param type at line %d", id.line); nexttok();
    Token nm = peek(); if(nm.kind != TK_IDENT) die("Expected param name after type at line %d", nm.line); nexttok();
    Var *v = var_alloc(nm.str, parse_type_name(id.str)); return v;
}
static Var *parse_typed_ident(){
    Token t = peek(); if(t.kind != TK_IDENT) die("Expected type name at line %d", t.line); nexttok();
    Token nm = peek(); if(nm.kind != TK_IDENT) die("Expected identifier after type at line %d", nm.line); nexttok();
    Var *v = var_alloc(nm.str, parse_type_name(t.str)); return v;
}

static Node *parse_block(){
    tok_expect(TK_LC);
    Node *blk = node_alloc(ND_BLOCK);
    Node *first = NULL, *last = NULL;
    while(!tok_accept(TK_RC)){
        Node *s = parse_statement();
        if(!first) first = last = s; else { last->next = s; last = s; }
    }
    blk->body = first;
    return blk;
}

static Node *parse_statement(){
    Token t = peek();
    if(t.kind == TK_KEYWORD_IF){
        nexttok();
        tok_expect(TK_LP);
        Node *cond = parse_expression(0);
        tok_expect(TK_RP);
        Node *thenb = parse_block();
        Node *elseb = NULL;
        if(peek().kind == TK_KEYWORD_ELSE){
            nexttok();
            if(peek().kind == TK_KEYWORD_IF){
                elseb = parse_statement();
            } else {
                elseb = parse_block();
            }
        }
        Node *n = node_alloc(ND_IF);
        n->cond = cond; n->then_block = thenb; n->else_block = elseb;
        return n;
    }
    if(t.kind == TK_KEYWORD_WHILE){
        nexttok();
        tok_expect(TK_LP);
        Node *cond = parse_expression(0);
        tok_expect(TK_RP);
        Node *body = parse_block();
        Node *n = node_alloc(ND_WHILE);
        n->cond = cond; n->while_body = body;
        return n;
    }
    if(t.kind == TK_KEYWORD_RETURN){
        nexttok();
        Node *n = node_alloc(ND_RETURN);
        if(!tok_accept(TK_SEMI)){
            n->ret_expr = parse_expression(0);
            tok_expect(TK_SEMI);
        }
        return n;
    }
    if(t.kind == TK_KEYWORD_PIN){
        nexttok();
        Var *v = parse_typed_ident();
        if(tok_accept(TK_ASSIGN)){
            Node *init = parse_expression(0);
            tok_expect(TK_SEMI);
            Node *n = node_alloc(ND_GLOBAL);
            v->is_global = true;
            v->init = init;
            n->gvar = v;
            return n;
        } else {
            tok_expect(TK_SEMI);
            Node *n = node_alloc(ND_GLOBAL);
            v->is_global = true;
            n->gvar = v;
            return n;
        }
    }
    if(t.kind == TK_KEYWORD_EXTERN || t.kind == TK_KEYWORD_FN || t.kind == TK_KEYWORD_IMPORT){
        return parse_top();
    }
    if(t.kind == TK_IDENT){
        Token t2 = P.tokens[P.idx+1];
        if(t2.kind == TK_IDENT){
            Var *v = parse_typed_ident();
            Node *n = node_alloc(ND_VARDECL);
            n->vname = STRDUP(v->name);
            n->ty = v->ty;
            if(tok_accept(TK_ASSIGN)){
                n->init = parse_expression(0);
            }
            tok_expect(TK_SEMI);
            return n;
        } else {
            Node *e = parse_expression(0);
            tok_expect(TK_SEMI);
            Node *n = node_alloc(ND_EXPR);
            n->lhs = e;
            return n;
        }
    }
    Node *e = parse_expression(0);
    tok_expect(TK_SEMI);
    Node *n = node_alloc(ND_EXPR);
    n->lhs = e;
    return n;
}

static Node *parse_top(){
    Token t = peek();
    if(t.kind == TK_KEYWORD_IMPORT){
        nexttok();
        Node *first = NULL, *last = NULL;
        while(1){
            Token tk = peek();
            char *p = NULL;
            if(tk.kind == TK_STRING){
                nexttok(); p = STRDUP(tk.str);
            } else if(tk.kind == TK_IDENT){
                nexttok(); p = malloc(strlen(tk.str)+5); strcpy(p, tk.str); strcat(p, ".zy");
            } else die("Unexpected token in import at line %d", tk.line);
            Node *n = node_alloc(ND_EXPR);
            n->sval = p;
            if(!first) first = last = n; else { last->next = n; last = n; }
            if(tok_accept(TK_COMMA)) continue;
            break;
        }
        tok_expect(TK_SEMI);
        return first;
    }
    if(t.kind == TK_KEYWORD_EXTERN){
        nexttok();
        tok_expect(TK_KEYWORD_FN);
        Token nm = peek(); if(nm.kind!=TK_IDENT) die("Expected extern fn name at line %d", nm.line); nexttok();
        Node *n = node_alloc(ND_EXTERN); n->name = STRDUP(nm.str);
        tok_expect(TK_LP);
        Var *firstp = NULL, *lastp = NULL;
        if(!tok_is(TK_RP)){
            while(1){
                Var *p = parse_param();
                if(!firstp) firstp = lastp = p; else { lastp->next = p; lastp = p; }
                if(tok_accept(TK_COMMA)) continue;
                break;
            }
        }
        tok_expect(TK_RP);
        tok_expect(TK_LT);
        Token rt = peek(); if(rt.kind != TK_IDENT) die("Expected return type in extern at line %d", rt.line); nexttok();
        n->ty = parse_type_name(rt.str);
        tok_expect(TK_GT);
        tok_expect(TK_SEMI);
        n->params = firstp;
        return n;
    }
    if(t.kind == TK_KEYWORD_FN){
        nexttok();
        Token nm = peek(); if(nm.kind!=TK_IDENT) die("Expected fn name at line %d", nm.line); nexttok();
        Node *fn = node_alloc(ND_FN); fn->name = STRDUP(nm.str);
        tok_expect(TK_LP);
        Var *firstp = NULL, *lastp = NULL;
        if(!tok_is(TK_RP)){
            while(1){
                Var *p = parse_param();
                if(!firstp) firstp = lastp = p; else { lastp->next = p; lastp = p; }
                if(tok_accept(TK_COMMA)) continue;
                break;
            }
        }
        tok_expect(TK_RP);
        tok_expect(TK_LT);
        Token rt = peek(); if(rt.kind != TK_IDENT) die("Expected return type in fn at line %d", rt.line); nexttok();
        fn->ty = parse_type_name(rt.str);
        tok_expect(TK_GT);
        fn->params = firstp;
        fn->body = parse_block();
        return fn;
    }
    die("Unknown top-level at line %d", t.line);
    return NULL;
}

static Token *tokenize_all(const char *src, int *out_count){
    Lexer L = { src, 0, 1 };
    Token *arr = NULL; int cap=0, cnt=0;
    while(1){
        Token t = lex_next(&L);
        if(cnt+1 >= cap){ cap = cap?cap*2:256; arr = realloc(arr, cap*sizeof(Token)); }
        arr[cnt++] = t;
        if(t.kind==TK_EOF) break;
    }
    *out_count = cnt;
    return arr;
}

static int tmp_counter = 0;
static int label_counter = 0;
static char *newtmp(){ char buf[64]; sprintf(buf,"%%t%d", tmp_counter++); return STRDUP(buf); }
static char *newlabel(){ char buf[64]; sprintf(buf,"l%d", label_counter++); return STRDUP(buf); }

typedef struct { Var *vars; buf out; buf decls; buf consts; int const_counter; bool did_return; } CodeGenCtx;
static CodeGenCtx CG;
static void cg_init(){ binit(&CG.out); binit(&CG.decls); binit(&CG.consts); CG.vars = NULL; CG.const_counter=0; CG.did_return=false; }

static Var *global_vars = NULL;
static void add_global_var(Var *g){ g->is_global = true; g->next = global_vars; global_vars = g; }

static char *emit_string_const(const char *s){
    int id = CG.const_counter++;
    char name[64]; sprintf(name,"@.str.%d", id);
    int len = strlen(s);
    char *esc = malloc(len*4+1); int p=0;
    for(int i=0;i<len;i++){
        unsigned char c = s[i];
        if(c=='\\'){ esc[p++]='\\'; esc[p++]='\\'; }
        else if(c=='"'){ esc[p++]='\\'; esc[p++]='"'; }
        else if((c>=32 && c<127)) esc[p++]=c;
        else { p += sprintf(esc+p, "\\%02x", c); }
    }
    esc[p]=0;
    bprintf(&CG.consts, "%s = constant [%d x i8] c\"%s\\00\"\n", name, len+1, esc);
    free(esc);
    char *ref = malloc(64); sprintf(ref, "%s", name);
    return ref;
}

static Var *find_var_inlist(Var *list, const char *name){
    for(Var *v=list; v; v=v->next) if(strcmp(v->name,name)==0) return v;
    return NULL;
}
static Var *find_var(const char *name){
    Var *v = find_var_inlist(CG.vars, name);
    if(v) return v;
    return find_var_inlist(global_vars, name);
}

struct FnProto { char *name; TypeKind ret; Var *params; struct FnProto *next; };
static struct FnProto *fn_protos = NULL;
static void add_fn_proto(const char *name, TypeKind ret, Var *params){ struct FnProto *p = malloc(sizeof(*p)); p->name = STRDUP(name); p->ret = ret; p->params = params; p->next = fn_protos; fn_protos = p; }

static char *cg_expr(Node *n);
static char *cg_lvalue(Node *n){
    if(n->kind == ND_IDENT){
        Var *v = find_var(n->sval);
        if(!v) die("Unknown variable '%s' in lvalue", n->sval);
        if(v->is_global){
            char *p = malloc(128); sprintf(p, "@%s", v->name); return p;
        } else return STRDUP(v->llvm_name);
    } else die("Invalid lvalue");
}

static bool is_float_type(TypeKind t){ return t==TY_FLOAT || t==TY_FLOAT64; }
static bool is_int_type(TypeKind t){
    return t==TY_I8 || t==TY_I16 || t==TY_I32 || t==TY_I64 || t==TY_U8 || t==TY_U16 || t==TY_U32 || t==TY_U64;
}
static bool is_unsigned_int(TypeKind t){
    return t==TY_U8 || t==TY_U16 || t==TY_U32 || t==TY_U64;
}
static int int_bits(TypeKind t){
    if(t==TY_I8||t==TY_U8) return 8;
    if(t==TY_I16||t==TY_U16) return 16;
    if(t==TY_I32||t==TY_U32) return 32;
    if(t==TY_I64||t==TY_U64) return 64;
    return 32;
}

static char *cg_to_i1(Node *expr, const char *val){
    if(expr->ty == TY_BOOL) return STRDUP(val);
    char *tmp = newtmp();
    if(is_int_type(expr->ty)){
        bprintf(&CG.out, "  %s = icmp ne %s %s, 0\n", tmp, tyname(expr->ty), val);
        return tmp;
    } else if(is_float_type(expr->ty)){
        bprintf(&CG.out, "  %s = fcmp une %s %s, 0.0\n", tmp, tyname(expr->ty), val);
        return tmp;
    } else if(expr->ty == TY_STRING){
        bprintf(&CG.out, "  %s = icmp ne %s %s, null\n", tmp, tyname(expr->ty), val);
        return tmp;
    } else {
        die("Cannot convert type to boolean in condition");
    }
    return NULL;
}

static char *cg_literal(Node *n, TypeKind *out_ty){
    if(n->sval == NULL) die("Empty literal");
    char *s = n->sval;
    bool isnum=true; bool hasdot=false;
    for(char *p=s; *p; p++){
        if(*p=='.') { hasdot=true; continue; }
        if(!isdigit((unsigned char)*p)) { isnum=false; break; }
    }
    if(isnum){
        if(hasdot){ *out_ty = TY_FLOAT64; char *tmp = newtmp(); bprintf(&CG.out, "  %s = fadd double %s, 0.0\n", tmp, s); return tmp; }
        else { *out_ty = TY_I32; char *val = malloc(64); sprintf(val, "%s", s); return val; }
    } else {
        *out_ty = TY_STRING;
        char *ref = emit_string_const(s);
        char *tmp = newtmp();
        bprintf(&CG.out, "  %s = getelementptr inbounds [%d x i8], [%d x i8]* %s, i32 0, i32 0\n", tmp, (int)(strlen(s)+1), (int)(strlen(s)+1), ref);
        return tmp;
    }
}

static char *emit_cast(TypeKind from, TypeKind to, const char *val){
    if(from == to) return STRDUP(val);
    char *res = newtmp();
    if(is_float_type(from) && is_float_type(to)){
        if(from==TY_FLOAT64 && to==TY_FLOAT) bprintf(&CG.out, "  %s = fptrunc double %s to %s\n", res, val, tyname(to));
        else if(from==TY_FLOAT && to==TY_FLOAT64) bprintf(&CG.out, "  %s = fpext float %s to %s\n", res, val, tyname(to));
        else bprintf(&CG.out, "  %s = fpext %s %s to %s\n", res, tyname(from), val, tyname(to));
        return res;
    }
    if(is_int_type(from) && is_int_type(to)){
        int fb = int_bits(from), tb = int_bits(to);
        bool funsigned = is_unsigned_int(from);
        if(tb > fb){
            if(funsigned) bprintf(&CG.out, "  %s = zext %s %s to %s\n", res, tyname(from), val, tyname(to));
            else bprintf(&CG.out, "  %s = sext %s %s to %s\n", res, tyname(from), val, tyname(to));
            return res;
        } else if(tb < fb){
            bprintf(&CG.out, "  %s = trunc %s %s to %s\n", res, tyname(from), val, tyname(to));
            return res;
        } else {
            return STRDUP(val);
        }
    }
    if(is_int_type(from) && is_float_type(to)){
        if(is_unsigned_int(from)) bprintf(&CG.out, "  %s = uitofp %s %s to %s\n", res, tyname(from), val, tyname(to));
        else bprintf(&CG.out, "  %s = sitofp %s %s to %s\n", res, tyname(from), val, tyname(to));
        return res;
    }
    if(is_float_type(from) && is_int_type(to)){
        if(is_unsigned_int(to)) bprintf(&CG.out, "  %s = fptoui %s %s to %s\n", res, tyname(from), val, tyname(to));
        else bprintf(&CG.out, "  %s = fptosi %s %s to %s\n", res, tyname(from), val, tyname(to));
        return res;
    }
    die("Unsupported cast from %s to %s", tyname(from), tyname(to));
    return NULL;
}

static char *cg_expr(Node *n){
    if(!n) return NULL;
    if(n->kind == ND_LITERAL){
        TypeKind t; char *v = cg_literal(n, &t);
        n->ty = t;
        return v;
    }
    if(n->kind == ND_IDENT){
        Var *v = find_var(n->sval);
        if(!v) die("Unknown identifier %s", n->sval);
        if(v->is_global){
            char *tmp = newtmp();
            bprintf(&CG.out, "  %s = load %s, %s* @%s\n", tmp, tyname(v->ty), tyname(v->ty), v->name);
            n->ty = v->ty;
            return tmp;
        } else {
            char *tmp = newtmp();
            bprintf(&CG.out, "  %s = load %s, %s* %s\n", tmp, tyname(v->ty), tyname(v->ty), v->llvm_name);
            n->ty = v->ty;
            return tmp;
        }
    }
    if(n->kind == ND_CALL){
        TypeKind target;
        if(try_parse_type_name(n->name, &target) && n->body && n->body->next == NULL){
            Node *arg = n->body;
            char *rv = cg_expr(arg);
            char *casted = emit_cast(arg->ty, target, rv);
            n->ty = target;
            return casted;
        }
        char *arglist = malloc(1); arglist[0]=0; int argc=0;
        for(Node *a=n->body; a; a=a->next){
            char *r = cg_expr(a);
            char tmpbuf[256];
            sprintf(tmpbuf, "%s %s", tyname(a->ty), r);
            size_t old = strlen(arglist);
            arglist = realloc(arglist, old + strlen(tmpbuf) + 4);
            if(argc) strcat(arglist,", ");
            strcat(arglist, tmpbuf);
            argc++;
        }
        char *res = newtmp();
        struct FnProto *p = fn_protos; TypeKind ret = TY_I32;
        while(p){ if(strcmp(p->name, n->name)==0){ ret = p->ret; break; } p=p->next; }
        if(ret == TY_VOID){
            bprintf(&CG.out, "  call %s @%s(%s)\n", tyname(ret), n->name, arglist);
            free(arglist);
            n->ty = TY_VOID;
            return STRDUP("");
        } else {
            bprintf(&CG.out, "  %s = call %s @%s(%s)\n", res, tyname(ret), n->name, arglist);
            free(arglist);
            n->ty = ret;
            return res;
        }
    }
    if(n->kind == ND_BINARY){
        if(n->op == OP_ASSIGN || (n->op>=OP_PLUS_EQ && n->op<=OP_SHR_EQ)){
            if(n->lhs->kind != ND_IDENT) die("Left side of assignment must be variable");
            Var *v = find_var(n->lhs->sval);
            if(!v) die("Unknown variable in assignment: %s", n->lhs->sval);
            char *rhs = cg_expr(n->rhs);
            if(n->op == OP_ASSIGN){
                if(v->is_global) bprintf(&CG.out, "  store %s %s, %s* @%s\n", tyname(v->ty), rhs, tyname(v->ty), v->name);
                else bprintf(&CG.out, "  store %s %s, %s* %s\n", tyname(v->ty), rhs, tyname(v->ty), v->llvm_name);
                n->ty = v->ty;
                return STRDUP(rhs);
            } else {
                char *lptr = cg_lvalue(n->lhs);
                char *old = newtmp();
                if(v->is_global) bprintf(&CG.out, "  %s = load %s, %s* @%s\n", old, tyname(v->ty), tyname(v->ty), v->name);
                else bprintf(&CG.out, "  %s = load %s, %s* %s\n", old, tyname(v->ty), tyname(v->ty), v->llvm_name);
                char *res = newtmp();
                int compound_op = n->op;
                if(compound_op==OP_PLUS_EQ || compound_op==OP_MINUS_EQ || compound_op==OP_MUL_EQ || compound_op==OP_DIV_EQ || compound_op==OP_MOD_EQ){
                    if(is_float_type(v->ty)){
                        const char *fop = compound_op==OP_PLUS_EQ?"fadd": compound_op==OP_MINUS_EQ?"fsub": compound_op==OP_MUL_EQ?"fmul": compound_op==OP_DIV_EQ?"fdiv": NULL;
                        if(!fop) die("Unsupported float compound op");
                        bprintf(&CG.out, "  %s = %s %s %s, %s\n", res, fop, tyname(v->ty), old, rhs);
                    } else {
                        const char *iop = compound_op==OP_PLUS_EQ?"add": compound_op==OP_MINUS_EQ?"sub": compound_op==OP_MUL_EQ?"mul": NULL;
                        if(compound_op==OP_DIV_EQ) iop = is_unsigned_int(v->ty) ? "udiv" : "sdiv";
                        if(compound_op==OP_MOD_EQ) iop = is_unsigned_int(v->ty) ? "urem" : "srem";
                        if(!iop) die("Unsupported int compound op");
                        bprintf(&CG.out, "  %s = %s %s %s, %s\n", res, iop, tyname(v->ty), old, rhs);
                    }
                } else if(compound_op==OP_AND_EQ||compound_op==OP_OR_EQ||compound_op==OP_XOR_EQ){
                    const char *iop = compound_op==OP_AND_EQ?"and": compound_op==OP_OR_EQ?"or": "xor";
                    bprintf(&CG.out, "  %s = %s %s %s, %s\n", res, iop, tyname(v->ty), old, rhs);
                } else if(compound_op==OP_SHL_EQ||compound_op==OP_SHR_EQ){
                    const char *iop = compound_op==OP_SHL_EQ?"shl": (is_unsigned_int(v->ty) ? "lshr" : "ashr");
                    bprintf(&CG.out, "  %s = %s %s %s, %s\n", res, iop, tyname(v->ty), old, rhs);
                } else die("Unknown compound op");
                if(v->is_global) bprintf(&CG.out, "  store %s %s, %s* @%s\n", tyname(v->ty), res, tyname(v->ty), v->name);
                else bprintf(&CG.out, "  store %s %s, %s* %s\n", tyname(v->ty), res, tyname(v->ty), v->llvm_name);
                n->ty = v->ty;
                return res;
            }
        }
        if(n->op==OP_EQ||n->op==OP_NE||n->op==OP_LT||n->op==OP_LE||n->op==OP_GT||n->op==OP_GE){
            char *la = cg_expr(n->lhs);
            char *rb = cg_expr(n->rhs);
            TypeKind t = n->lhs->ty;
            char *res = newtmp();
            if(is_float_type(t)){
                const char *cmp = NULL;
                if(n->op==OP_EQ) cmp = "oeq";
                else if(n->op==OP_NE) cmp = "one";
                else if(n->op==OP_LT) cmp = "olt";
                else if(n->op==OP_LE) cmp = "ole";
                else if(n->op==OP_GT) cmp = "ogt";
                else if(n->op==OP_GE) cmp = "oge";
                else die("Unknown float cmp");
                bprintf(&CG.out, "  %s = fcmp %s %s %s, %s\n", res, cmp, tyname(t), la, rb);
            } else {
                const char *cmp = NULL;
                bool use_unsigned = is_unsigned_int(n->lhs->ty) || is_unsigned_int(n->rhs->ty);
                if(n->op==OP_EQ) cmp = "eq";
                else if(n->op==OP_NE) cmp = "ne";
                else if(n->op==OP_LT) cmp = use_unsigned ? "ult" : "slt";
                else if(n->op==OP_LE) cmp = use_unsigned ? "ule" : "sle";
                else if(n->op==OP_GT) cmp = use_unsigned ? "ugt" : "sgt";
                else if(n->op==OP_GE) cmp = use_unsigned ? "uge" : "sge";
                else die("Unknown int cmp");
                bprintf(&CG.out, "  %s = icmp %s %s %s, %s\n", res, cmp, tyname(t), la, rb);
            }
            n->ty = TY_BOOL;
            return res;
        }
        char *la = cg_expr(n->lhs);
        char *rb = cg_expr(n->rhs);
        TypeKind t = n->lhs->ty;
        n->ty = t;
        char *res = newtmp();
        switch(n->op){
            case OP_ADD: if(is_float_type(t)) bprintf(&CG.out,"  %s = fadd %s %s, %s\n", res, tyname(t), la, rb); else bprintf(&CG.out,"  %s = add %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_SUB: if(is_float_type(t)) bprintf(&CG.out,"  %s = fsub %s %s, %s\n", res, tyname(t), la, rb); else bprintf(&CG.out,"  %s = sub %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_MUL: if(is_float_type(t)) bprintf(&CG.out,"  %s = fmul %s %s, %s\n", res, tyname(t), la, rb); else bprintf(&CG.out,"  %s = mul %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_DIV: if(is_float_type(t)) bprintf(&CG.out,"  %s = fdiv %s %s, %s\n", res, tyname(t), la, rb); else bprintf(&CG.out,"  %s = %s %s %s, %s\n", res, is_unsigned_int(t) ? "udiv" : "sdiv", tyname(t), la, rb); break;
            case OP_MOD: bprintf(&CG.out,"  %s = %s %s %s, %s\n", res, is_unsigned_int(t) ? "urem" : "srem", tyname(t), la, rb); break;
            case OP_BAND: bprintf(&CG.out,"  %s = and %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_BOR: bprintf(&CG.out,"  %s = or %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_BXOR: bprintf(&CG.out,"  %s = xor %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_SHL: bprintf(&CG.out,"  %s = shl %s %s, %s\n", res, tyname(t), la, rb); break;
            case OP_SHR: bprintf(&CG.out,"  %s = %s %s %s, %s\n", res, is_unsigned_int(t) ? "lshr" : "ashr", tyname(t), la, rb); break;
            default: die("Unimplemented binary op %d", n->op);
        }
        return res;
    }
    if(n->kind == ND_UNARY){
        char *r = cg_expr(n->rhs);
        if(n->op == '-') {
            char *res = newtmp();
            if(n->rhs->ty == TY_FLOAT || n->rhs->ty==TY_FLOAT64)
                bprintf(&CG.out, "  %s = fsub %s 0.0, %s\n", res, tyname(n->rhs->ty), r);
            else
                bprintf(&CG.out, "  %s = sub %s 0, %s\n", res, tyname(n->rhs->ty), r);
            n->ty = n->rhs->ty;
            return res;
        }
        die("Unsupported unary op");
    }
    die("Unhandled expr kind %d", n->kind);
    return NULL;
}

static void cg_stmt(Node *n);
static void cg_stmt_list(Node *n){ for(Node *s = n; s; s = s->next) cg_stmt(s); }
static void cg_create_local(Var *v){ char *alloc = newtmp(); bprintf(&CG.out, "  %s = alloca %s\n", alloc, tyname(v->ty)); v->llvm_name = STRDUP(alloc); v->next = CG.vars; CG.vars = v; }

static void cg_stmt(Node *n){
    if(!n) return;
    switch(n->kind){
        case ND_BLOCK: cg_stmt_list(n->body); break;
        case ND_VARDECL:{
            Var *v = var_alloc(n->vname, n->ty);
            cg_create_local(v);
            if(n->init){
                char *r = cg_expr(n->init);
                bprintf(&CG.out, "  store %s %s, %s* %s\n", tyname(v->ty), r, tyname(v->ty), v->llvm_name);
            }
            break;
        }
        case ND_EXPR: cg_expr(n->lhs); break;
        case ND_RETURN:{
            CG.did_return = true;
            if(n->ret_expr){
                char *r = cg_expr(n->ret_expr);
                bprintf(&CG.out, "  ret %s %s\n", tyname(n->ret_expr->ty), r);
            } else bprintf(&CG.out, "  ret void\n");
            break;
        }
        case ND_IF:{
            char *condv = cg_expr(n->cond);
            char *condi = cg_to_i1(n->cond, condv);
            char *l_then = newlabel(); char *l_else = newlabel(); char *l_end = newlabel();
            bprintf(&CG.out, "  br i1 %s, label %%%s, label %%%s\n", condi, l_then, l_else);
            bprintf(&CG.out, "%s:\n", l_then);
            cg_stmt(n->then_block);
            bprintf(&CG.out, "  br label %%%s\n", l_end);
            bprintf(&CG.out, "%s:\n", l_else);
            if(n->else_block) cg_stmt(n->else_block);
            bprintf(&CG.out, "  br label %%%s\n", l_end);
            bprintf(&CG.out, "%s:\n", l_end);
            break;
        }
        case ND_WHILE:{
            char *l_cond = newlabel(); char *l_body = newlabel(); char *l_end = newlabel();
            bprintf(&CG.out, "  br label %%%s\n", l_cond);
            bprintf(&CG.out, "%s:\n", l_cond);
            char *cv = cg_expr(n->cond);
            char *ci = cg_to_i1(n->cond, cv);
            bprintf(&CG.out, "  br i1 %s, label %%%s, label %%%s\n", ci, l_body, l_end);
            bprintf(&CG.out, "%s:\n", l_body);
            cg_stmt(n->while_body);
            bprintf(&CG.out, "  br label %%%s\n", l_cond);
            bprintf(&CG.out, "%s:\n", l_end);
            break;
        }
        case ND_GLOBAL: {
            add_global_var(n->gvar);
            if(n->gvar->init){
                if(n->gvar->init->kind == ND_LITERAL){
                    bool isnumeric=true; for(char *p=n->gvar->init->sval; *p; p++){ if(*p=='.' || !isdigit((unsigned char)*p)){ isnumeric=false; break; } }
                    if(isnumeric) bprintf(&CG.decls, "@%s = global %s %s\n", n->gvar->name, tyname(n->gvar->ty), n->gvar->init->sval);
                    else { char *ref = emit_string_const(n->gvar->init->sval); bprintf(&CG.decls, "@%s = global %s 0\n", n->gvar->name, tyname(n->gvar->ty)); (void)ref; }
                } else bprintf(&CG.decls, "@%s = global %s 0\n", n->gvar->name, tyname(n->gvar->ty));
            } else bprintf(&CG.decls, "@%s = global %s 0\n", n->gvar->name, tyname(n->gvar->ty));
            break;
        }
        default: die("Unhandled stmt kind in cg_stmt: %d", n->kind);
    }
}

static void cg_emit_extern(Node *e){
    add_fn_proto(e->name, e->ty, e->params);
    bprintf(&CG.decls, "declare %s @%s(", tyname(e->ty), e->name);
    bool first=true;
    for(Var *p=e->params; p; p=p->next){ if(!first) bprintf(&CG.decls, ", "); bprintf(&CG.decls, "%s", tyname(p->ty)); first=false; }
    bprintf(&CG.decls, ")\n");
}

static void cg_emit_function(Node *fn){
    add_fn_proto(fn->name, fn->ty, fn->params);
    bprintf(&CG.decls, "define %s @%s(", tyname(fn->ty), fn->name);
    bool first=true;
    for(Var *p = fn->params; p; p=p->next){ if(!first) bprintf(&CG.decls, ", "); bprintf(&CG.decls, "%s %%%s", tyname(p->ty), p->name); first=false; }
    bprintf(&CG.decls, ") {\n");
    CG.vars = NULL; tmp_counter = 0; CG.did_return = false;
    bput(&CG.out, "entry:\n");
    for(Var *p = fn->params; p; p=p->next){ Var *lv = var_alloc(p->name, p->ty); cg_create_local(lv); bprintf(&CG.out, "  store %s %%%s, %s* %s\n", tyname(p->ty), p->name, tyname(p->ty), lv->llvm_name); }
    cg_stmt(fn->body);
    if(!CG.did_return){
        if(fn->ty == TY_VOID) bprintf(&CG.out, "  ret void\n"); else bprintf(&CG.out, "  ret %s 0\n", tyname(fn->ty));
    }
    bprintf(&CG.decls, "%s", CG.out.data);
    bput(&CG.decls, "}\n\n");
    free(CG.out.data); binit(&CG.out);
}

static void cg_emit_global(Node *g){
    Var *v = g->gvar; add_global_var(v);
    if(v->init){
        if(v->init->kind == ND_LITERAL){
            bool isnumeric=true; for(char *p=v->init->sval; *p; p++){ if(*p=='.' || !isdigit((unsigned char)*p)){ isnumeric=false; break; } }
            if(isnumeric) bprintf(&CG.decls, "@%s = global %s %s\n", v->name, tyname(v->ty), v->init->sval);
            else { char *ref = emit_string_const(v->init->sval); bprintf(&CG.decls, "@%s = global %s 0\n", v->name, tyname(v->ty)); (void)ref; }
        } else bprintf(&CG.decls, "@%s = global %s 0\n", v->name, tyname(v->ty));
    } else bprintf(&CG.decls, "@%s = global %s 0\n", v->name, tyname(v->ty));
}

typedef struct TopList { Node *n; struct TopList *next; } TopList;
static TopList *append_top(TopList *list, Node *n){ TopList *t = malloc(sizeof(*t)); t->n = n; t->next = NULL; if(!list) return t; TopList *p=list; while(p->next) p=p->next; p->next = t; return list; }

static TopList *compile_file_to_tops(const char *path){
    if(file_loaded(path)) return NULL;
    char *src = read_file(path);
    if(!src){
        if(!strchr(path,'.')){
            char tmp[1024]; sprintf(tmp, "%s.zy", path);
            src = read_file(tmp);
            if(src) path = STRDUP(tmp);
        }
        if(!src) die("Could not read file %s", path);
    }
    mark_loaded(path);
    int tcount; Token *toks = tokenize_all(src, &tcount);
    Parser saved = P;
    P.tokens = toks; P.tokcount = tcount; P.idx = 0;
    TopList *tops = NULL;
    while(!tok_is(TK_EOF)){
        Node *top = parse_top();
        for(Node *it = top; it; it = it->next){
            if(it->kind == ND_EXPR && it->sval){
                TopList *imp = compile_file_to_tops(it->sval);
                for(TopList *p=imp;p;p=p->next) tops = append_top(tops, p->n);
            } else {
                tops = append_top(tops, it);
            }
        }
    }
    P = saved;
    return tops;
}

static void compile_tops_to_ll(TopList *tops, const char *outpath){
    cg_init();
    for(TopList *p = tops; p; p = p->next){
        Node *n = p->n;
        if(n->kind == ND_GLOBAL) cg_emit_global(n);
        else if(n->kind == ND_EXTERN) cg_emit_extern(n);
        else if(n->kind == ND_FN) cg_emit_function(n);
    }
    FILE *f = fopen(outpath,"wb"); if(!f) die("Could not open output file");
    if(CG.consts.len) fprintf(f, "%s\n", CG.consts.data);
    for(Var *g = global_vars; g; g = g->next) fprintf(f, "@%s = global %s 0\n", g->name, tyname(g->ty));
    fprintf(f, "%s\n", CG.decls.data);
    fclose(f);
}

static void usage(){ printf("ZyndrC\nUsage: Zyndr input.zy -o out.ll\n"); exit(1); }

int main(int argc, char **argv){
    if(argc < 2) usage();
    const char *infile = NULL; const char *outfile = "a.ll";
    for(int i=1;i<argc;i++){
        if(strcmp(argv[i],"-o")==0){ if(i+1<argc) { outfile = argv[++i]; } else die("-o requires arg"); }
        else if(!infile) infile = argv[i];
        else usage();
    }
    if(!infile) usage();
    if(!strchr(infile,'.')){
        char tmp[1024]; sprintf(tmp,"%s.zy", infile);
        if(!read_file(infile) && read_file(tmp)) infile = strdup(tmp);
    }
    TopList *tops = compile_file_to_tops(infile);
    if(!tops) die("No top-level nodes parsed");
    compile_tops_to_ll(tops, outfile);
    printf("Wrote %s\n", outfile);
    return 0;
}
