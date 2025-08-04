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

predicate expression(struct expression *e; int v) =
    e != 0 &*&
    malloc_block_expression(e) &*&
    e->tag |-> ?tag &*&
    (
        tag == 0 ?
            e->value |-> v &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _
        : tag == 1 ?
            e->value |-> _ &*&
            e->operand_neg |-> ?op_neg &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            expression(op_neg, ?op_neg_val) &*&
            v == -op_neg_val
        : tag == 2 ?
            e->value |-> _ &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> ?op1 &*&
            e->operand2 |-> ?op2 &*&
            expression(op1, ?op1_val) &*&
            expression(op2, ?op2_val) &*&
            v == op1_val + op2_val
        : false
    );

@*/


// TODO: make this function pass the verification
/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expression as an operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1, ?v1) &*& expression(operand2, ?v2);
    //@ ensures expression(result, v1 + v2);
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    return addition;
}