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
// Predicate to represent an expression
predicate expr(struct expression *e; int tag) =
    e != 0 &*&
    malloc_block_expression(e) &*&
    e->tag |-> tag &*&
    tag == 0 ?
        e->value |-> ?v
    : tag == 1 ?
        e->operand_neg |-> ?neg &*& expr(neg, ?neg_tag)
    :
        e->operand1 |-> ?op1 &*& expr(op1, ?op1_tag) &*&
        e->operand2 |-> ?op2 &*& expr(op2, ?op2_tag);

// Predicate for a literal expression specifically
predicate literal_expr(struct expression *e; int value) =
    expr(e, 0) &*& e->value |-> value;
@*/

/*@
// Helper lemma to convert from expr to literal_expr
lemma void expr_to_literal_expr(struct expression *e)
    requires expr(e, 0) &*& e->value |-> ?v;
    ensures literal_expr(e, v);
{
    close literal_expr(e, v);
}
@*/

/**
 * Description:
 * The create_literal function allocates an expression with the tag for literal (0) and value as given.
 *
 * @param value: the value of this literal expression.
 *
 * It makes sure that the return value is an expression of literal with its value set.
 */
struct expression *create_literal(int value)
//@ requires true;
//@ ensures literal_expr(result, value);
{
    struct expression *literal = malloc(sizeof(struct expression));
    //@ if (literal == 0) abort();
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    //@ close expr(literal, 0);
    //@ expr_to_literal_expr(literal);
    return literal;
}