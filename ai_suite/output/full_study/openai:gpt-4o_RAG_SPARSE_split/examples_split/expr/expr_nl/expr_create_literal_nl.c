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

//@ predicate expression_literal(struct expression *e, int value) =
//@     e->tag |-> 0 &*& e->value |-> value &*& e->operand_neg |-> _ &*& e->operand1 |-> _ &*& e->operand2 |-> _ &*& malloc_block_expression(e);

/*@
predicate expression(struct expression *e) =
    e == 0 ? true :
    e->tag |-> ?tag &*&
    tag == 0 ? expression_literal(e, ?value) :
    tag == 1 ? e->operand_neg |-> ?neg &*& expression(neg) :
    tag == 2 ? e->operand1 |-> ?op1 &*& e->operand2 |-> ?op2 &*& expression(op1) &*& expression(op2) :
    false;
@*/

// TODO: make this function pass the verification
/***
 * Description:
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.

It makes sure that the return value is an expression of literal with its value set.
*/
//@ requires true;
//@ ensures expression_literal(result, value);
struct expression *create_literal(int value)
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    literal->operand_neg = 0;
    literal->operand1 = 0;
    literal->operand2 = 0;
    //@ close expression_literal(literal, value);
    return literal;
}