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
// Define a predicate for the expression structure
predicate expression(struct expression *expr; int result) =
    expr->tag |-> ?tag &*&
    expr->value |-> ?value &*&
    expr->operand_neg |-> ?operand_neg &*&
    expr->operand1 |-> ?operand1 &*&
    expr->operand2 |-> ?operand2 &*&
    malloc_block_expression(expr) &*&
    tag == 0 ?
        result == value
    : tag == 1 ?
        expression(operand_neg, ?neg_result) &*&
        neg_result >= INT_MIN + 1 &*&
        result == 0 - neg_result
    : tag == 2 ?
        expression(operand1, ?result1) &*&
        expression(operand2, ?result2) &*&
        ((result2 > 0 && result1 <= INT_MAX - result2) || 
         (result1 > 0 && result2 <= INT_MAX - result1) ||
         (result2 < 0 && result1 >= INT_MIN - result2) ||
         (result1 < 0 && result2 >= INT_MIN - result1)) &*&
        result == result1 + result2
    :
        false;
@*/

/***
 * Description:
The evaluate function calculates the value of an given expression recursively and return the such value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
//@ requires expression(expression, ?result);
//@ ensures expression(expression, result) &*& result == result;
{
    int result = 0;
    //@ open expression(expression, _);
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
    //@ close expression(expression, result);
    return result;
}