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

/*@
predicate expression(struct expression *expr, int value) =
    expr->tag |-> ?tag &*& malloc_block_expression(expr) &*&
    tag == 0 ? expr->value |-> value &*& expr->operand_neg |-> _ &*& expr->operand1 |-> _ &*& expr->operand2 |-> _ :
    tag == 1 ? expr->value |-> _ &*& expr->operand_neg |-> ?operand_neg &*& expression(operand_neg, ?operand_neg_value) 
                &*& value == 0 - operand_neg_value &*& expr->operand1 |-> _ &*& expr->operand2 |-> _ :
    tag == 2 &*& expr->value |-> _ &*& expr->operand_neg |-> _ &*& expr->operand1 |-> ?operand1 &*& expr->operand2 |-> ?operand2
             &*& expression(operand1, ?operand1_value) &*& expression(operand2, ?operand2_value) &*& value == operand1_value + operand2_value;
@*/


struct expression *create_literal(int value)
    //@ requires true;
    //@ ensures expression(result, value);
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    //@ close expression(literal, value);
    return literal;
}



struct expression *create_negation(struct expression *operand)
    //@ requires expression(operand, ?operandValue);
    //@ ensures expression(result, 0 - operandValue);
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    //@ close expression(negation, 0 - operandValue);
    return negation;
}


struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1, ?value1) &*& expression(operand2, ?value2);
    //@ ensures expression(result, value1 + value2);
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    //@ close expression(addition, value1 + value2);
    return addition;
}


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