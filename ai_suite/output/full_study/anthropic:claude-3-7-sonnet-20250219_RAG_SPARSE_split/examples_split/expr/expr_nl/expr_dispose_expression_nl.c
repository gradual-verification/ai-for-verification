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
predicate expression(struct expression *expr; int depth) =
    expr == 0 ?
        depth == 0
    :
        expr->tag |-> ?tag &*&
        expr->value |-> ?value &*&
        expr->operand_neg |-> ?neg &*&
        expr->operand1 |-> ?op1 &*&
        expr->operand2 |-> ?op2 &*&
        malloc_block_expression(expr) &*&
        tag == 0 ?
            depth == 1
        : tag == 1 ?
            expression(neg, ?negDepth) &*&
            depth == negDepth + 1
        : tag == 2 ?
            expression(op1, ?op1Depth) &*&
            expression(op2, ?op2Depth) &*&
            depth == (op1Depth > op2Depth ? op1Depth : op2Depth) + 1
        :
            false;
@*/

/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
void dispose_expression(struct expression *expression)
//@ requires expression(expression, ?depth);
//@ ensures true;
{
    //@ open expression(expression, depth);
    if (expression == 0) {
        return;
    }
    
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