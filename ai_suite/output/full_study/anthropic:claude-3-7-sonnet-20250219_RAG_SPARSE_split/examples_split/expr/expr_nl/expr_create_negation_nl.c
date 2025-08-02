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
predicate expression(struct expression *e; int v) =
    e != 0 &*&
    e->tag |-> ?tag &*&
    e->value |-> ?value &*&
    e->operand_neg |-> ?operand_neg &*&
    e->operand1 |-> ?operand1 &*&
    e->operand2 |-> ?operand2 &*&
    malloc_block_expression(e) &*&
    tag == 0 ?
        v == value &*&
        operand_neg == 0 &*&
        operand1 == 0 &*&
        operand2 == 0
    : tag == 1 ?
        expression(operand_neg, ?operand_neg_value) &*&
        v == -operand_neg_value &*&
        operand1 == 0 &*&
        operand2 == 0
    : tag == 2 ?
        expression(operand1, ?operand1_value) &*&
        expression(operand2, ?operand2_value) &*&
        v == operand1_value + operand2_value &*&
        operand_neg == 0
    : false;
@*/

/***
 * Description:
The create_negation function allocates an negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
struct expression *create_negation(struct expression *operand)
//@ requires expression(operand, ?operand_value);
//@ ensures expression(result, -operand_value) &*& expression(operand, operand_value);
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    //@ negation->value = 0; // Not needed for the computation but helps with the predicate
    //@ negation->operand1 = 0;
    //@ negation->operand2 = 0;
    //@ close expression(negation, -operand_value);
    return negation;
}