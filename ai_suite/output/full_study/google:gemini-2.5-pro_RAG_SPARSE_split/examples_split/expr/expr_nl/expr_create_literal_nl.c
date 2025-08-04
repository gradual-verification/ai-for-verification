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
// An abstract syntax tree for expressions.
inductive ast =
    | TNull
    | TLiteral(int value)
    | TNeg(ast operand)
    | TAdd(ast left, ast right);

// A predicate that relates a C expression struct to an abstract syntax tree.
predicate expression_pred(struct expression *e; ast t) =
    e == 0 ?
        t == TNull
    :
        malloc_block_expression(e) &*&
        e->tag |-> ?tag &*&
        (tag == 0 ?
            e->value |-> ?v &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            t == TLiteral(v)
        : tag == 1 ?
            e->value |-> _ &*&
            e->operand_neg |-> ?op_neg &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            expression_pred(op_neg, ?t_neg) &*&
            t == TNeg(t_neg)
        : tag == 2 ?
            e->value |-> _ &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> ?op1 &*&
            e->operand2 |-> ?op2 &*&
            expression_pred(op1, ?t1) &*&
            expression_pred(op2, ?t2) &*&
            t == TAdd(t1, t2)
        :
            false
        );
@*/


// TODO: make this function pass the verification
/***
 * Description:
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.

It makes sure that the return value is an exoression of literal with its value set.
*/
struct expression *create_literal(int value)
    //@ requires true;
    //@ ensures expression_pred(result, TLiteral(value));
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    //@ close expression_pred(literal, TLiteral(value));
    return literal;
}