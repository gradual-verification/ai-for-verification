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
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expression as an operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    return addition;
}

