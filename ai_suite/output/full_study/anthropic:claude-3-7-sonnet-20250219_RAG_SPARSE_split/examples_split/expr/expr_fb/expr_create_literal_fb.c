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
    expr->tag |-> ?tag &*&
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
    literal->operand_neg = 0;
    literal->operand1 = 0;
    literal->operand2 = 0;
    //@ close expression(literal, value);
    return literal;
}