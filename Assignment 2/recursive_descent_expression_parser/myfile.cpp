/*
 * Ahmed Tamer       - 20220013
 * Ahmed Abdelnabi   - 20220027
 * Ahmed Alaaeldin   - 20220028
 * George Raafat     - 20220097
 * AbdulRahman Tarek - 20221096
 *
 * Extended BNF Grammar for Group Expressions
 * (James Hein, "Theory of Computation: An Introduction", Pages 459-460)
 *
 *   expr -> term { '.' term }
 *   term -> atom { '^-1' }
 *   atom -> '(' expr ')' | 'e' | VAR
 *
 * Reduction rules from pages 459-460:
 *   (R1)  e.x         ->  x
 *   (R2)  x.e         ->  x
 *   (R3)  x^-1.x      ->  e
 *   (R4)  x.x^-1      ->  e
 *   (R5)  e^-1        ->  e
 *   (R6)  x^-1^-1     ->  x
 *   (R7)  y^-1.(y.z)  ->  z
 *   (R8)  y.(y^-1.z)  ->  z
 *   (R9)  (x.y).z     ->  x.(y.z)
 *   (R10) (x.y)^-1    ->  y^-1.x^-1
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
using namespace std;

// =============================================================================
// Token
// =============================================================================

enum TokenType
{
    VAR,
    IDENTITY,
    DOT,
    INV_OP,
    LPAREN,
    RPAREN,
    ENDFILE,
    TOK_ERROR
};

struct Token
{
    TokenType type;
    char      var_name;

    Token() : type(TOK_ERROR), var_name('\0') {}
};

// =============================================================================
// Scanner
// =============================================================================

struct Scanner
{
    const char* input;
    int         pos;
    int         length;

    Scanner(const char* s) : input(s), pos(0), length((int)strlen(s)) {}

    char peek(int offset = 0) const
    {
        int i = pos + offset;
        return (i < length) ? input[i] : '\0';
    }

    void advance(int n = 1) { pos += n; }

    void skipWhitespace()
    {
        while (pos < length && (input[pos] == ' ' || input[pos] == '\t'))
            ++pos;
    }

    Token nextToken()
    {
        skipWhitespace();
        Token t;

        if (pos >= length) { t.type = ENDFILE; return t; }

        char c = peek();

        if (c == 'e')
        {
            t.type = IDENTITY;
            advance();
            return t;
        }

        if (c >= 'a' && c <= 'z')
        {
            t.type     = VAR;
            t.var_name = c;
            advance();
            return t;
        }

        if (c == '.') { t.type = DOT;    advance(); return t; }
        if (c == '(') { t.type = LPAREN; advance(); return t; }
        if (c == ')') { t.type = RPAREN; advance(); return t; }

        if (c == '^' && peek(1) == '-' && peek(2) == '1')
        {
            t.type = INV_OP;
            advance(3);
            return t;
        }

        t.type = TOK_ERROR;
        advance();
        return t;
    }
};

// =============================================================================
// Parse Tree
// =============================================================================

enum NodeKind
{
    PRODUCT_NODE,
    INVERSE_NODE,
    IDENTITY_NODE,
    VAR_NODE
};

#define MAX_CHILDREN 2

struct TreeNode
{
    NodeKind  kind;
    char      var_name;
    TreeNode* child[MAX_CHILDREN];

    explicit TreeNode(NodeKind k) : kind(k), var_name('\0')
    {
        child[0] = child[1] = 0;
    }
};

void destroyTree(TreeNode* node)
{
    if (!node) return;
    for (int i = 0; i < MAX_CHILDREN; ++i) destroyTree(node->child[i]);
    delete node;
}

TreeNode* cloneTree(TreeNode* node)
{
    if (!node) return 0;
    TreeNode* copy = new TreeNode(node->kind);
    copy->var_name = node->var_name;
    for (int i = 0; i < MAX_CHILDREN; ++i)
        copy->child[i] = cloneTree(node->child[i]);
    return copy;
}

bool treesEqual(TreeNode* a, TreeNode* b)
{
    if (!a && !b) return true;
    if (!a || !b) return false;
    if (a->kind != b->kind) return false;
    if (a->kind == VAR_NODE && a->var_name != b->var_name) return false;
    for (int i = 0; i < MAX_CHILDREN; ++i)
        if (!treesEqual(a->child[i], b->child[i])) return false;
    return true;
}

// =============================================================================
// printTree
// =============================================================================

void printTree(TreeNode* node, int depth)
{
    if (!node) return;

    for (int i = 1; i < depth; ++i) printf("   ");
    if (depth > 0) printf("|--");

    switch (node->kind)
    {
        case PRODUCT_NODE:  printf("product\n");             break;
        case INVERSE_NODE:  printf("inverse\n");             break;
        case IDENTITY_NODE: printf("e\n");                   break;
        case VAR_NODE:      printf("%c\n", node->var_name);  break;
    }

    for (int i = 0; i < MAX_CHILDREN; ++i)
        printTree(node->child[i], depth + 1);
}

// =============================================================================
// printExpr
// =============================================================================

void printExpr(TreeNode* node)
{
    if (!node) return;

    switch (node->kind)
    {
        case VAR_NODE:
            printf("%c", node->var_name);
            break;

        case IDENTITY_NODE:
            printf("e");
            break;

        case INVERSE_NODE:
        {
            TreeNode* c = node->child[0];
            bool atomic = (c->kind == VAR_NODE || c->kind == IDENTITY_NODE);
            if (atomic) { printExpr(c); }
            else        { printf("("); printExpr(c); printf(")"); }
            printf("^-1");
            break;
        }

        case PRODUCT_NODE:
        {
            TreeNode* L = node->child[0];
            TreeNode* R = node->child[1];

            if (L->kind == PRODUCT_NODE)
            { printf("("); printExpr(L); printf(")"); }
            else
            { printExpr(L); }

            printf(".");

            if (R->kind == PRODUCT_NODE)
            { printf("("); printExpr(R); printf(")"); }
            else
            { printExpr(R); }
            break;
        }
    }
}

// =============================================================================
// Recursive Descent Parser
// =============================================================================

struct Parser
{
    Scanner scanner;
    Token   current;

    explicit Parser(const char* input) : scanner(input)
    {
        current = scanner.nextToken();
    }

    void match(TokenType expected)
    {
        if (current.type != expected)
        {
            fprintf(stderr, "Parse error: unexpected token.\n");
            exit(1);
        }
        current = scanner.nextToken();
    }

    TreeNode* expr()
    {
        TreeNode* tree = term();
        while (current.type == DOT)
        {
            match(DOT);
            TreeNode* right = term();
            TreeNode* node = new TreeNode(PRODUCT_NODE);
            node->child[0] = tree;
            node->child[1] = right;
            tree = node;
        }
        return tree;
    }

    TreeNode* term()
    {
        TreeNode* tree = atom();
        while (current.type == INV_OP)
        {
            match(INV_OP);
            TreeNode* node = new TreeNode(INVERSE_NODE);
            node->child[0] = tree;
            tree = node;
        }
        return tree;
    }

    TreeNode* atom()
    {
        if (current.type == LPAREN)
        {
            match(LPAREN);
            TreeNode* tree = expr();
            match(RPAREN);
            return tree;
        }
        if (current.type == IDENTITY)
        {
            match(IDENTITY);
            return new TreeNode(IDENTITY_NODE);
        }
        if (current.type == VAR)
        {
            TreeNode* node = new TreeNode(VAR_NODE);
            node->var_name = current.var_name;
            match(VAR);
            return node;
        }

        fprintf(stderr, "Parse error: expected atom (variable, 'e', or '(').\n");
        exit(1);
        return 0;
    }

    TreeNode* parse()
    {
        TreeNode* tree = expr();
        if (current.type != ENDFILE)
            fprintf(stderr, "Warning: input not fully consumed.\n");
        return tree;
    }
};

// =============================================================================
// Reduction Rules
// =============================================================================

TreeNode* makeIdentity()             { return new TreeNode(IDENTITY_NODE); }
TreeNode* makeInverse(TreeNode* c)
{
    TreeNode* n = new TreeNode(INVERSE_NODE);
    n->child[0] = c;
    return n;
}
TreeNode* makeProduct(TreeNode* a, TreeNode* b)
{
    TreeNode* n = new TreeNode(PRODUCT_NODE);
    n->child[0] = a;
    n->child[1] = b;
    return n;
}

TreeNode* tryR1(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    if (n->child[0]->kind != IDENTITY_NODE) return 0;
    TreeNode* keep = n->child[1];
    n->child[1] = 0;
    destroyTree(n);
    return keep;
}

TreeNode* tryR2(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    if (n->child[1]->kind != IDENTITY_NODE) return 0;
    TreeNode* keep = n->child[0];
    n->child[0] = 0;
    destroyTree(n);
    return keep;
}

TreeNode* tryR3(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    TreeNode* L = n->child[0];
    TreeNode* R = n->child[1];
    if (L->kind != INVERSE_NODE) return 0;
    if (!treesEqual(L->child[0], R)) return 0;
    destroyTree(n);
    return makeIdentity();
}

TreeNode* tryR4(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    TreeNode* L = n->child[0];
    TreeNode* R = n->child[1];
    if (R->kind != INVERSE_NODE) return 0;
    if (!treesEqual(R->child[0], L)) return 0;
    destroyTree(n);
    return makeIdentity();
}

TreeNode* tryR5(TreeNode* n)
{
    if (n->kind != INVERSE_NODE) return 0;
    if (n->child[0]->kind != IDENTITY_NODE) return 0;
    destroyTree(n);
    return makeIdentity();
}

TreeNode* tryR6(TreeNode* n)
{
    if (n->kind != INVERSE_NODE) return 0;
    if (n->child[0]->kind != INVERSE_NODE) return 0;
    TreeNode* keep = n->child[0]->child[0];
    n->child[0]->child[0] = 0;
    destroyTree(n);
    return keep;
}

TreeNode* tryR7(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    TreeNode* L = n->child[0];
    TreeNode* R = n->child[1];
    if (L->kind != INVERSE_NODE)         return 0;
    if (R->kind != PRODUCT_NODE)         return 0;
    if (!treesEqual(L->child[0], R->child[0])) return 0;

    TreeNode* keep = R->child[1];
    R->child[1] = 0;
    destroyTree(n);
    return keep;
}

TreeNode* tryR8(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    TreeNode* L = n->child[0];
    TreeNode* R = n->child[1];
    if (R->kind != PRODUCT_NODE)         return 0;
    if (R->child[0]->kind != INVERSE_NODE) return 0;
    if (!treesEqual(R->child[0]->child[0], L)) return 0;

    TreeNode* keep = R->child[1];
    R->child[1] = 0;
    destroyTree(n);
    return keep;
}

TreeNode* tryR9(TreeNode* n)
{
    if (n->kind != PRODUCT_NODE) return 0;
    TreeNode* L = n->child[0];
    if (L->kind != PRODUCT_NODE) return 0;

    TreeNode* x = L->child[0];
    TreeNode* y = L->child[1];
    TreeNode* z = n->child[1];

    L->child[0] = L->child[1] = 0;
    n->child[0] = n->child[1] = 0;
    destroyTree(n);

    return makeProduct(x, makeProduct(y, z));
}

TreeNode* tryR10(TreeNode* n)
{
    if (n->kind != INVERSE_NODE) return 0;
    TreeNode* P = n->child[0];
    if (P->kind != PRODUCT_NODE) return 0;

    TreeNode* x = P->child[0];
    TreeNode* y = P->child[1];

    P->child[0] = P->child[1] = 0;
    n->child[0] = 0;
    destroyTree(n);

    return makeProduct(makeInverse(y), makeInverse(x));
}

TreeNode* tryAllRulesAtRoot(TreeNode* n)
{
    TreeNode* r;
    if ((r = tryR1 (n))) return r;
    if ((r = tryR2 (n))) return r;
    if ((r = tryR3 (n))) return r;
    if ((r = tryR4 (n))) return r;
    if ((r = tryR5 (n))) return r;
    if ((r = tryR6 (n))) return r;
    if ((r = tryR7 (n))) return r;
    if ((r = tryR8 (n))) return r;
    if ((r = tryR9 (n))) return r;
    if ((r = tryR10(n))) return r;
    return 0;
}

TreeNode* reduceStep(TreeNode* n, bool* changed)
{
    if (!n || *changed) return n;

    TreeNode* r = tryAllRulesAtRoot(n);
    if (r)
    {
        *changed = true;
        return r;
    }

    for (int i = 0; i < MAX_CHILDREN && !*changed; ++i)
    {
        if (n->child[i])
            n->child[i] = reduceStep(n->child[i], changed);
    }
    return n;
}

// =============================================================================
// runTest  —  organised output
// =============================================================================

void runTest(int testNumber, const char* input)
{
    // ── Header ──────────────────────────────────────────────────────────────
    printf("Test %d: %s\n", testNumber, input);

    // ── Parse ────────────────────────────────────────────────────────────────
    Parser    p(input);
    TreeNode* tree = p.parse();

    // ── Initial parse tree ───────────────────────────────────────────────────
    printf("\nParse tree:\n");
    printTree(tree, 0);

    // ── Reduce fully (no intermediate output) ────────────────────────────────
    while (true)
    {
        bool changed = false;
        tree = reduceStep(tree, &changed);
        if (!changed) break;
    }

    // ── Fully-reduced tree + expression ──────────────────────────────────────
    printf("\nReduced parse tree:\n");
    printTree(tree, 0);
    printf("Reduced expression: ");
    printExpr(tree);
    printf("\n");

    // ── Separator ────────────────────────────────────────────────────────────
    printf("==========================================\n");

    destroyTree(tree);
}

// =============================================================================
// main
// =============================================================================

int main()
{
    if (!freopen("input.txt", "r", stdin))
    {
        fprintf(stderr, "Error: could not open input.txt\n");
        return 1;
    }
    if (!freopen("output.txt", "w", stdout))
    {
        fprintf(stderr, "Error: could not open output.txt\n");
        return 1;
    }

    char line[1024];
    int  testNumber = 1;

    while (fgets(line, sizeof(line), stdin))
    {
        int len = (int)strlen(line);
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r'))
            line[--len] = '\0';

        if (len == 0) continue;

        runTest(testNumber++, line);
    }

    return 0;
}
