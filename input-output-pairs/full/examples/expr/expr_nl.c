#include "stdlib.h"

struct expression {
    // tag = 0 means a literal with value
    // tag = 1 means it is an negated of operand_neg
    // tag = 2 means it is an addition of operand1 and operand2
    int tag;
    int value;
    struct expression *operand_neg;
    struct expression *operand1;
    struct expression *operand2;
};

/***
 * Description:
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.
*/
struct expression *create_literal(int value)
    //@ requires true;
    //@ ensures expression(result, value);
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    return literal;
}

/***
 * Description:
The create_negation function allocates an negated expression for the given expression as an operand,
, meaning that the value of returned expression is the negation of the value in the operand.

@param operand: the given expression as an operand to be negated.
*/
struct expression *create_negation(struct expression *operand)
    //@ requires expression(operand, ?operandValue);
    //@ ensures expression(result, 0 - operandValue);
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    return negation;
}

/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands,
, meaning that the value of returned expression is the sum of value of two given expressions.

@param operand1 and operand2: the two given expression as an operands to be added.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1, ?value1) &*& expression(operand2, ?value2);
    //@ ensures expression(result, value1 + value2);
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    return addition;
}

/***
 * Description:
The evaluate function calculates the value of an given expression recursively and return the such value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
    //@ requires expression(expression, ?value);
    //@ ensures expression(expression, value) &*& result == value;
{
    int result = 0;
    int tag = expression->tag;
    if (tag == 0)
        result = expression->value;
    else if (tag == 1) {
        int v = evaluate(expression->operand_neg);
        if (v < 0 - INT_MAX) {abort();}
        result = 0 - v;
    } else {
        int v1 = evaluate(expression->operand1);
        int v2 = evaluate(expression->operand2);
        if ((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
            || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1)) { abort();}
        result = v1 + v2;
    }
    return result;
}

/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
void dispose_expression(struct expression *expression)
    //@ requires expression(expression, _);
    //@ ensures true;
{
    int tag = expression->tag;
    if (tag == 0) {
        free(expression);
    } else if (tag == 1) {
        dispose_expression(expression->operand_neg);
        free(expression);
    } else {
        dispose_expression(expression->operand1);
        dispose_expression(expression->operand2);
        free(expression);
    }
}

/***
 * Description:
The main function initializes several expressions using the `create_literal`, `create_negation`, and `create_addition` functions, 
evaluates the final expression, asserts the result, disposes of the expressions' memory, and returns 0.
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    // Build 1 + -(5 + 3);
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