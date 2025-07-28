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
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.

It makes sure that the return value is an exoression of literal with its value set.
*/
struct expression *create_literal(int value)
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    return literal;
}

