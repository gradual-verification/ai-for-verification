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

// TODO: make this function pass the verification
int evaluate(struct expression *expression)
    //@ requires expression(expression, ?value);
    //@ ensures expression(expression, value) &*& result == value;
{
    int result = 0;
    int tag = expression->tag;
    if (tag == 0) {
        result = expression->value;
    } else if (tag == 1) {
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