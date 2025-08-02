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
    e->tag |-> ?tag &*&
    tag == 0 ?
        e->value |-> _ &*& e->operand_neg |-> _ &*& e->operand1 |-> _ &*& e->operand2 |-> _
    : tag == 1 ?
        e->operand_neg |-> ?operand_neg &*& expression(operand_neg) &*& e->value |-> _ &*& e->operand1 |-> _ &*& e->operand2 |-> _
    : tag == 2 ?
        e->operand1 |-> ?operand1 &*& expression(operand1) &*& e->operand2 |-> ?operand2 &*& expression(operand2) &*& e->value |-> _
    : false;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_negation function allocates a negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
/*@
requires expression(operand);
ensures expression(result) &*& result->tag == 1 &*& result->operand_neg |-> operand;
@*/
struct expression *create_negation(struct expression *operand)
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    //@ close expression(negation);
    return negation;
}