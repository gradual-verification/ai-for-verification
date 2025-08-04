#include "stdlib.h"

/*@
predicate expression_footprint(struct expression *e;) =
    e == 0 ?
        true
    :
        malloc_block_expression(e) &*&
        e->tag |-> ?tag &*&
        e->value |-> _ &*&
        e->operand_neg |-> ?op_neg &*&
        e->operand1 |-> ?op1 &*&
        e->operand2 |-> ?op2 &*&
        (tag == 0 ?
            true
        : tag == 1 ?
            op_neg != 0 &*& expression_footprint(op_neg)
        : tag == 2 ?
            op1 != 0 &*& expression_footprint(op1) &*&
            op2 != 0 &*& expression_footprint(op2)
        :
            false
        );
@*/

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


// TODO: make this function pass the verification
/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
void dispose_expression(struct expression *expression)
    //@ requires expression != 0 &*& expression_footprint(expression);
    //@ ensures true;
{
    //@ open expression_footprint(expression);
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