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


// TODO: make this function pass the verification
/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
void dispose_expression(struct expression *expression)
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

