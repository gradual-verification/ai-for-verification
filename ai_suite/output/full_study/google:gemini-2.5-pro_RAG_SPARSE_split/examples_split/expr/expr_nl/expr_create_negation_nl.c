#include "stdlib.h"

/*@
// Predicate to model the expression data structure and its value.
// It is a recursive predicate that defines the ownership and properties of an expression tree.
// - e: a pointer to the expression struct.
// - val: the mathematical value of the expression.
predicate expression(struct expression *e, int val);
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

/*@
predicate expression(struct expression *e, int val) =
    e == 0 ?
        false // We assume expressions are never null.
    :
        malloc_block_expression(e) &*&
        e->tag |-> ?tag &*&
        (tag == 0 ?
            // Case 1: Literal expression
            e->value |-> val &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _
        : tag == 1 ?
            // Case 2: Negation expression
            e->value |-> _ &*&
            e->operand_neg |-> ?op_neg &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            expression(op_neg, ?op_val) &*&
            val == -op_val
        : tag == 2 ?
            // Case 3: Addition expression
            e->value |-> _ &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> ?op1 &*&
            e->operand2 |-> ?op2 &*&
            expression(op1, ?op1_val) &*&
            expression(op2, ?op2_val) &*&
            val == op1_val + op2_val
        :
            // Any other tag is invalid.
            false
        );
@*/


// TODO: make this function pass the verification
/***
 * Description:
The create_negation function allocates an negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
struct expression *create_negation(struct expression *operand)
    //@ requires expression(operand, ?v);
    //@ ensures expression(result, -v);
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    return negation;
}