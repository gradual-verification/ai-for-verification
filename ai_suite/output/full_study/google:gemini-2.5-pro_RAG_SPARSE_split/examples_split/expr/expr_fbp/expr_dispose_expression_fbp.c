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


void dispose_expression(struct expression *expression)
    //@ requires expression(expression, _);
    //@ ensures true;
{
    //@ open expression(expression, _);
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