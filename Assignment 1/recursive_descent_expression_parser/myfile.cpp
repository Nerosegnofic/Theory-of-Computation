/*
 * Ahmed Tamer       - 20220013
 * Ahmed Abdelnabi   - 20220027
 * Ahmed Alaaeldin   - 20220028
 * George Raafat     - 20220097
 * AbdulRahman Tarek - 20221096
 * =============================================================================
 * Extended BNF Grammar for Group Expressions
 * (James Hein, "Theory of Computation: An Introduction", Pages 459-460)
 * =============================================================================
 *
 *   expr -> term { '.' term }
 *   term -> atom { '^-1' }
 *   atom -> '(' expr ')' | 'e' | VAR
 *
 * Terminals:
 *   VAR   = any lowercase letter 'a'..'z' except 'e'
 *   'e'   = identity element of the group
 *   '.'   = group product operator (left-associative, binary)
 *   '^-1' = group inverse operator (postfix; left-chained when repeated)
 *   '('   = left parenthesis
 *   ')'   = right parenthesis
 *
 * Associativity:
 *   '.'   is left-associative:  x.y.z  parses as  (x.y).z
 *   '^-1' is left-chained:      x^-1^-1  parses as  (x^-1)^-1
 *
 * Reduction rules captured from pages 459-460:
 *   e.x         ->  x              (left identity)
 *   x.e         ->  x              (right identity)
 *   x^-1.x      ->  e              (left inverse)
 *   x.x^-1      ->  e              (right inverse)
 *   e^-1        ->  e              (inverse of identity)
 *   x^-1^-1     ->  x              (involution / double inverse)
 *   y^-1.(y.z)  ->  z              (left cancellation)
 *   y.(y^-1.z)  ->  z              (right cancellation)
 *   (x.y).z     ->  x.(y.z)        (associativity)
 *   (x.y)^-1    ->  y^-1.x^-1     (inverse of product)
 *
 * Example (left-hand side of last equation, page 460):
 *   Input:  ((x.y^-1).z)^-1
 *   Output:
 *     inverse
 *     |--product
 *        |--product
 *           |--x
 *           |--inverse
 *              |--y
 *        |--z
 * =============================================================================
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
    VAR,        // lowercase letter other than 'e'
    IDENTITY,   // the letter 'e'
    DOT,        // '.'
    INV_OP,     // '^-1'  (entire postfix inverse, read as 3 characters)
    LPAREN,     // '('
    RPAREN,     // ')'
    ENDFILE,    // end of the input string
    TOK_ERROR   // unrecognized character
};

struct Token
{
    TokenType type;
    char      var_name;    // valid only when type == VAR

    Token() : type(TOK_ERROR), var_name('\0') {}
};

// =============================================================================
// Scanner (Lexer)
// Reads characters from a null-terminated C string, produces tokens.
// =============================================================================

struct Scanner
{
    const char* input;
    int         pos;
    int         length;

    Scanner(const char* s) : input(s), pos(0), length((int)strlen(s)) {}

    // Return character at pos+offset without advancing; '\0' past end.
    char peek(int offset = 0) const
    {
        int i = pos + offset;
        return (i < length) ? input[i] : '\0';
    }

    void advance(int n = 1) { pos += n; }

    // Skip spaces and tabs only (newlines are not expected in single-line input).
    void skipWhitespace()
    {
        while (pos < length && (input[pos] == ' ' || input[pos] == '\t'))
            ++pos;
    }

    Token nextToken()
    {
        skipWhitespace();
        Token t;

        if (pos >= length)
        {
            t.type = ENDFILE;
            return t;
        }

        char c = peek();

        // Identity element 'e' must be checked before general VAR.
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

        if (c == '.') { t.type = DOT;    advance();    return t; }
        if (c == '(') { t.type = LPAREN; advance();    return t; }
        if (c == ')') { t.type = RPAREN; advance();    return t; }

        // Inverse operator: must be exactly '^', '-', '1'.
        if (c == '^' && peek(1) == '-' && peek(2) == '1')
        {
            t.type = INV_OP;
            advance(3);
            return t;
        }

        // Anything else is an error token; consume one character.
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
    PRODUCT_NODE,    // binary: child[0] '.' child[1]
    INVERSE_NODE,    // unary:  child[0] '^-1'
    IDENTITY_NODE,   // leaf:   'e'
    VAR_NODE         // leaf:   single variable letter
};

#define MAX_CHILDREN 2

struct TreeNode
{
    NodeKind  kind;
    char      var_name;              // valid only when kind == VAR_NODE
    TreeNode* child[MAX_CHILDREN];

    explicit TreeNode(NodeKind k) : kind(k), var_name('\0')
    {
        child[0] = child[1] = 0;
    }
};

// =============================================================================
// Print Parse Tree
//
// Format (depth 0 has no prefix; each deeper level adds "   " then "|--"):
//   depth 0:  label
//   depth 1:  |--label
//   depth 2:     |--label          (3 spaces + "|--")
//   depth 3:        |--label       (6 spaces + "|--")
// =============================================================================

void printTree(TreeNode* node, int depth)
{
    if (!node) return;

    for (int i = 1; i < depth; ++i) printf("   ");
    if (depth > 0) printf("|--");

    switch (node->kind)
    {
        case PRODUCT_NODE:  printf("product\n");          break;
        case INVERSE_NODE:  printf("inverse\n");          break;
        case IDENTITY_NODE: printf("e\n");                break;
        case VAR_NODE:      printf("%c\n", node->var_name); break;
    }

    for (int i = 0; i < MAX_CHILDREN; ++i)
        printTree(node->child[i], depth + 1);
}

// =============================================================================
// Destroy Parse Tree (post-order)
// =============================================================================

void destroyTree(TreeNode* node)
{
    if (!node) return;
    for (int i = 0; i < MAX_CHILDREN; ++i) destroyTree(node->child[i]);
    delete node;
}

// =============================================================================
// Recursive Descent Parser
// Implements the EBNF grammar defined at the top of this file.
// =============================================================================

struct Parser
{
    Scanner scanner;
    Token   current;        // lookahead token

    explicit Parser(const char* input) : scanner(input)
    {
        current = scanner.nextToken();    // prime the lookahead
    }

    // Consume the current token if it matches 'expected'; abort on mismatch.
    void match(TokenType expected)
    {
        if (current.type != expected)
        {
            fprintf(stderr, "Parse error: unexpected token.\n");
            exit(1);
        }
        current = scanner.nextToken();
    }

    // -------------------------------------------------------------------------
    // expr -> term { '.' term }         (left-associative product)
    // -------------------------------------------------------------------------
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

    // -------------------------------------------------------------------------
    // term -> atom { '^-1' }            (postfix inverse, left-chained)
    // -------------------------------------------------------------------------
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

    // -------------------------------------------------------------------------
    // atom -> '(' expr ')' | 'e' | VAR
    // -------------------------------------------------------------------------
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
        return 0;    // unreachable; silences compiler warning
    }

    // -------------------------------------------------------------------------
    // Entry point: parse a complete expression and return its tree.
    // -------------------------------------------------------------------------
    TreeNode* parse()
    {
        TreeNode* tree = expr();

        if (current.type != ENDFILE)
            fprintf(stderr, "Warning: input not fully consumed.\n");

        return tree;
    }
};

// =============================================================================
// Run a single test case: print input, then print parse tree.
// =============================================================================

void runTest(int num, const char* input)
{
    printf("--------------------------------------------------\n");
    printf("Test %2d: %s\n", num, input);
    printf("Parse Tree:\n");

    Parser    p(input);
    TreeNode* tree = p.parse();
    printTree(tree, 0);
    printf("\n");
    destroyTree(tree);
}

// =============================================================================
// Main — 25 test cases covering all reduction rules from pages 459-460.
// Every case exercises a distinct grammar feature or combination thereof.
// =============================================================================

int main()
{
    // --- Basic identity rules (e.x -> x, x.e -> x) ---
    runTest( 1, "e.x");
    runTest( 2, "x.e");

    // --- Basic inverse rules (x^-1.x -> e, x.x^-1 -> e) ---
    runTest( 3, "x^-1.x");
    runTest( 4, "x.x^-1");

    // --- Inverse of identity (e^-1 -> e) ---
    runTest( 5, "e^-1");

    // --- Double inverse / involution (x^-1^-1 -> x) ---
    runTest( 6, "x^-1^-1");

    // --- Cancellation rules from page 460 ---
    runTest( 7, "y^-1.(y.z)");
    runTest( 8, "y.(y^-1.z)");

    // --- Associativity: (x.y).z -> x.(y.z) ---
    runTest( 9, "(x.y).z");
    runTest(10, "x.(y.z)");

    // --- Inverse of product: (x.y)^-1 -> y^-1.x^-1 ---
    runTest(11, "(x.y)^-1");

    // --- Page 460 worked example: left-hand side ---
    runTest(12, "((x.y^-1).z)^-1");

    // --- Page 460 worked example: right-hand side ---
    runTest(13, "(z^-1.y).x^-1");

    // --- Left-associativity of '.' over three and four operands ---
    runTest(14, "x.y.z");
    runTest(15, "a.b.c.d");

    // --- Triple inverse (applied three times to the same atom) ---
    runTest(16, "e^-1^-1^-1");

    // --- Double inverse then product ---
    runTest(17, "x^-1^-1.x");

    // --- Right-nested products ---
    runTest(18, "a.(b.(c.d))");

    // --- Product of two bracketed sub-expressions with inverses ---
    runTest(19, "(a.b^-1).(c^-1.d)");

    // --- Double inverse of a grouped product ---
    runTest(20, "((a.b).c)^-1^-1");

    // --- Inverse of a product of inverses ---
    runTest(21, "(x^-1.y^-1)^-1");

    // --- Alternating products and inverses ---
    runTest(22, "x.y^-1.z.w^-1");

    // --- Compound expression derived from page 460 chain of reductions ---
    runTest(23, "((x.y)^-1.(y.z)).z^-1");

    // --- Identity-like compound: (x.y^-1)^-1 . (y.x^-1) ---
    runTest(24, "(x.y^-1)^-1.(y.x^-1)");

    // --- Chain of cancellations across three variable pairs ---
    runTest(25, "(a^-1.b).(b^-1.c).(c^-1.a)");

    return 0;
}