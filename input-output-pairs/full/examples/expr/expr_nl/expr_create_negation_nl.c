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
The create_negation function allocates an negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
struct expression *create_negation(struct expression *operand)
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    return negation;
}

