#include "stdlib.h"

struct literal {
    int tag;
    int value;
};

struct negation {
    int tag;
    void *operand;
};

struct addition {
    int tag;
    void *operand1;
    void *operand2;
};

/* Description
    - Behavior: This function creates a literal expression with the given integer value.
    - Parameters: 
        -`int value` - The integer value to be stored in the literal expression.
*/
struct literal *create_literal(int value)
{
    struct literal *literal = malloc(sizeof(struct literal));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    return literal;
}

/* Description
    - Behavior: Creates a new `struct negation` instance with the specified `operand`.
    - Parameters:
        - `operand`: A pointer to the operand that will be negated.
*/
struct negation *create_negation(void *operand)
{
    struct negation *negation = malloc(sizeof(struct negation));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand = operand;
    return negation;
}

/* Description
    - Behavior: Creates a new `struct addition` instance with the specified operands.
    - Parameters:
        - `operand1`: A pointer to the first operand of the addition.
        - `operand2`: A pointer to the second operand of the addition.
*/
struct addition *create_addition(void *operand1, void *operand2)
{
    struct addition *addition = malloc(sizeof(struct addition));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    return addition;
}

/* Description
    - Behavior: Evaluates the expression represented by the given pointer.
    - Parameters:
        - `expression`: A pointer to the expression to be evaluated.
*/
int evaluate(void *expression)
{
    int result = 0;
    int tag = *((int *)expression);
    if (tag == 0)
        result = ((struct literal *)expression)->value;
    else if (tag == 1) {
        int v = evaluate(((struct negation *)expression)->operand);
        result = 0 - v;
    } else {
        struct addition *addition = expression;
        int v1 = evaluate(addition->operand1);
        int v2 = evaluate(addition->operand2);
        result = v1 + v2;
    }
    return result;
}

/* Description
    - Behavior: Frees the memory allocated for the expression and its components.
    - Parameters:
        - `expression`: A pointer to the expression to be disposed.
*/
void dispose_expression(void *expression)
{
    int tag = *((int *)expression);
    if (tag == 0) {
        free((struct literal *)expression);
    } else if (tag == 1) {
        struct negation *negation = expression;
        dispose_expression(negation->operand);
        free(negation);
    } else {
        struct addition *addition = expression;
        dispose_expression(addition->operand1);
        dispose_expression(addition->operand2);
        free(addition);
    }
}

/* Description
    - Behavior: initializes several expressions using the `create_literal`, `create_negation`, and `create_addition` functions, evaluates the final expression, asserts the result, disposes of the expressions' memory, and returns 0.
*/
int main()
{
    void *e1 = create_literal(1);
    void *e2 = create_literal(5);
    void *e3 = create_literal(3);
    void *e4 = create_addition(e2, e3);
    void *e5 = create_negation(e4);
    void *e6 = create_addition(e1, e5);
    
    int value = evaluate(e6);
    assert(value == 0 - 7);
    
    dispose_expression(e6);
    return 0;
}