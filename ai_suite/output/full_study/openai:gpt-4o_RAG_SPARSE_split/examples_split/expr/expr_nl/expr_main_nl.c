#include "stdlib.h"

struct expression {
    // tag = 0 means a literal with value
    // tag = 1 means it is a negated of operand_neg
    // tag = 2 means it is an addition of operand1 and operand2
    int tag;
    int value;
    struct expression *operand_neg;
    struct expression *operand1;
    struct expression *operand2;
};

/*@
predicate expression(struct expression *e, int value) =
    e->tag |-> ?tag &*&
    tag == 0 ?
        e->value |-> value &*& e->operand_neg |-> _ &*& e->operand1 |-> _ &*& e->operand2 |-> _ &*& malloc_block_expression(e)
    : tag == 1 ?
        e->value |-> _ &*& e->operand_neg |-> ?op_neg &*& e->operand1 |-> _ &*& e->operand2 |-> _ &*& expression(op_neg, ?v) &*& value == -v &*& malloc_block_expression(e)
    : tag == 2 ?
        e->value |-> _ &*& e->operand_neg |-> _ &*& e->operand1 |-> ?op1 &*& e->operand2 |-> ?op2 &*& expression(op1, ?v1) &*& expression(op2, ?v2) &*& value == v1 + v2 &*& malloc_block_expression(e)
    : false;
@*/

/***
 * Description:
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.

It makes sure that the return value is an expression of literal with its value set.
*/
struct expression *create_literal(int value)
    //@ requires true;
    //@ ensures expression(result, value);
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    literal->operand_neg = 0;
    literal->operand1 = 0;
    literal->operand2 = 0;
    //@ close expression(literal, value);
    return literal;
}

/***
 * Description:
The create_negation function allocates a negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
struct expression *create_negation(struct expression *operand)
    //@ requires expression(operand, ?v);
    //@ ensures expression(result, -v);
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    negation->operand1 = 0;
    negation->operand2 = 0;
    //@ close expression(negation, -v);
    return negation;
}

/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expressions as operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1, ?v1) &*& expression(operand2, ?v2);
    //@ ensures expression(result, v1 + v2);
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    addition->operand_neg = 0;
    //@ close expression(addition, v1 + v2);
    return addition;
}

/***
 * Description:
The evaluate function calculates the value of a given expression recursively and returns the value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
    //@ requires expression(expression, ?v);
    //@ ensures expression(expression, v) &*& result == v;
{
    int result = 0;
    int tag = expression->tag;
    if (tag == 0) {
        result = expression->value;
    } else if (tag == 1) {
        int v = evaluate(expression->operand_neg);
        if (v < 0 - INT_MAX) { abort(); }
        result = 0 - v;
    } else {
        int v1 = evaluate(expression->operand1);
        int v2 = evaluate(expression->operand2);
        if ((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
            || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1)) { abort(); }
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

// TODO: make this function pass the verification
/***
 * Description:
The main function tests the operations of expression. 
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    // Build 1 + -(5 + 3);
    struct expression *e1 = create_literal(1);
    struct expression *e2 = create_literal(5);
    struct expression *e3 = create_literal(3);
    struct expression *e4 = create_addition(e2, e3);
    struct expression *e5 = create_negation(e4);
    struct expression *e6 = create_addition(e1, e5);
    
    int value = evaluate(e6);
    assert(value == 0 - 7);
    
    dispose_expression(e6);
    return 0;
}