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
 * Terminals:
 *   VAR   = any lowercase letter 'a'..'z' except 'e'
 *   'e'   = identity element of the group
 *   '.'   = group product operator
 *   '^-1' = group inverse operator (postfix)
 *   '('   = left parenthesis
 *   ')'   = right parenthesis
 *
 * Associativity:
 *   '.'   is left-associative:  x.y.z    parses as (x.y).z
 *   '^-1' is left-chained:      x^-1^-1  parses as (x^-1)^-1
 *
 * Example:
 *   Input:  ((x.y^-1).z)^-1
 *   Output:
 *     inverse
 *     |--product
 *        |--product
 *           |--x
 *           |--inverse
 *              |--y
 *        |--z
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>

// =============================================================================
// Token
// =============================================================================

enum TokenType
{
    VAR,        // lowercase letter other than 'e'
    IDENTITY,   // the letter 'e'
    DOT,        // '.'
    INV_OP,     // '^-1' consumed as a single 3-character unit
    LPAREN,     // '('
    RPAREN,     // ')'
    ENDFILE,    // end of input
    TOK_ERROR   // unrecognized character
};

struct Token
{
    TokenType type;
    char      var_name;    // meaningful only when type == VAR

    Token() : type(TOK_ERROR), var_name('\0') {}
};

// =============================================================================
// Scanner
// Walks a null-terminated C string one logical token at a time.
// =============================================================================

struct Scanner
{
    const char* input;
    int         pos;
    int         length;

    Scanner(const char* s) : input(s), pos(0), length((int)strlen(s)) {}

    // Look ahead without consuming; returns '\0' past the end.
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

        if (pos >= length)
        {
            t.type = ENDFILE;
            return t;
        }

        char c = peek();

        // 'e' must be checked before the general VAR case.
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

        // Inverse operator is always exactly three characters: ^, -, 1.
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
    PRODUCT_NODE,    // binary:  child[0] '.' child[1]
    INVERSE_NODE,    // unary:   child[0] '^-1'
    IDENTITY_NODE,   // leaf:    'e'
    VAR_NODE         // leaf:    single variable letter
};

#define MAX_CHILDREN 2

struct TreeNode
{
    NodeKind  kind;
    char      var_name;              // meaningful only when kind == VAR_NODE
    TreeNode* child[MAX_CHILDREN];

    explicit TreeNode(NodeKind k) : kind(k), var_name('\0')
    {
        child[0] = child[1] = 0;
    }
};

// Post-order deletion to avoid accessing freed children.
void destroyTree(TreeNode* node)
{
    if (!node) return;
    for (int i = 0; i < MAX_CHILDREN; ++i) destroyTree(node->child[i]);
    delete node;
}

// =============================================================================
// printTree
//
// Indentation scheme:
//   depth 0  ->  no indent, no prefix
//   depth 1  ->  |--
//   depth 2  ->     |--   (3 spaces per level above 1)
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
// Recursive Descent Parser
// Each grammar rule maps directly to one member function.
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

    // expr -> term { '.' term }
    // Left-associativity is achieved by accumulating into a left-leaning tree
    // inside the while loop rather than using right recursion.
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

    // term -> atom { '^-1' }
    // Repeated inverses wrap the previous result, giving left-chaining:
    // x^-1^-1 becomes INVERSE(INVERSE(x)).
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

    // atom -> '(' expr ')' | 'e' | VAR
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
// runTest
// =============================================================================

void runTest(int num, const char* input)
{
    printf("--------------------------------------------------\n");
    printf("Test %2d: %s\n", num, input);
    printf("Parse Tree:\n");

    Parser    p(input);
    TreeNode* tree = p.parse();
    printTree(tree, 0);
    destroyTree(tree);
}

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
    int  testNum = 1;

    while (fgets(line, sizeof(line), stdin))
    {
        int len = (int)strlen(line);
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r'))
            line[--len] = '\0';

        if (len == 0) continue;

        runTest(testNum++, line);
    }

    return 0;
}
