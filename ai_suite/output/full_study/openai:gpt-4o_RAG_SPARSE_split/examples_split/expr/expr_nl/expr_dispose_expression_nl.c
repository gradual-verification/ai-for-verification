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
predicate expression(struct expression *e) =
    e == 0 ? true :
    e->tag |-> ?tag &*&
    tag == 0 ?
        e->value |-> _ &*& malloc_block_expression(e)
    : tag == 1 ?
        e->operand_neg |-> ?neg &*& expression(neg) &*& malloc_block_expression(e)
    : tag == 2 ?
        e->operand1 |-> ?op1 &*& expression(op1) &*&
        e->operand2 |-> ?op2 &*& expression(op2) &*& malloc_block_expression(e)
    : false;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
/*@
requires expression(expression);
ensures true;
@*/
void dispose_expression(struct expression *expression)
{
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