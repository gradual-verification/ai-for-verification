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
predicate expression(struct expression *e) =
    e->tag |-> ?tag &*&
    tag == 0 ?
        e->value |-> _ &*& e->operand_neg |-> _ &*& e->operand1 |-> _ &*& e->operand2 |-> _ &*& malloc_block_expression(e)
    : tag == 1 ?
        e->value |-> _ &*& e->operand_neg |-> ?neg &*& expression(neg) &*& e->operand1 |-> _ &*& e->operand2 |-> _ &*& malloc_block_expression(e)
    : tag == 2 ?
        e->value |-> _ &*& e->operand_neg |-> _ &*& e->operand1 |-> ?op1 &*& expression(op1) &*& e->operand2 |-> ?op2 &*& expression(op2) &*& malloc_block_expression(e)
    : false;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expression as an operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1) &*& expression(operand2);
    //@ ensures expression(result) &*& result->tag == 2 &*& result->operand1 == operand1 &*& result->operand2 == operand2;
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    //@ close expression(addition);
    return addition;
}