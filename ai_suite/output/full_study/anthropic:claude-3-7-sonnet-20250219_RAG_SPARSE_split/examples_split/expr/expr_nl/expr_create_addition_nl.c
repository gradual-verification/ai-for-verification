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
predicate expression(struct expression *e; int value) =
    e->tag |-> ?tag &*&
    e->value |-> value &*&
    e->operand_neg |-> ?neg &*&
    e->operand1 |-> ?op1 &*&
    e->operand2 |-> ?op2 &*&
    malloc_block_expression(e) &*&
    (tag == 0 ? true :
     tag == 1 ? expression(neg, ?neg_val) &*& value == -neg_val :
     tag == 2 ? expression(op1, ?val1) &*& expression(op2, ?val2) &*& value == val1 + val2 :
     false);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expression as an operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
/*@
    requires expression(operand1, ?val1) &*& expression(operand2, ?val2);
    ensures expression(result, val1 + val2) &*& result != 0;
@*/
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    addition->value = operand1->value + operand2->value;
    //@ close expression(addition, val1 + val2);
    return addition;
}