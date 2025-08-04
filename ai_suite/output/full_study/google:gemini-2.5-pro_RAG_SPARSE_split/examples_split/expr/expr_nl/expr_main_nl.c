#include "stdlib.h"
#include "assert.h"

/*@
#include <limits.h>

inductive expr_view =
    lit(int v)
  | neg(expr_view op)
  | add(expr_view op1, expr_view op2);

fixpoint int eval_view(expr_view ev) {
    switch(ev) {
        case lit(v): return v;
        case neg(op): return -eval_view(op);
        case add(op1, op2): return eval_view(op1) + eval_view(op2);
    }
}

fixpoint bool is_safe_to_eval(expr_view ev) {
    switch(ev) {
        case lit(v):
            return true;
        case neg(op):
            return is_safe_to_eval(op) && eval_view(op) != INT_MIN;
        case add(op1, op2):
            return is_safe_to_eval(op1) && is_safe_to_eval(op2) &&
                   (long)eval_view(op1) + (long)eval_view(op2) >= INT_MIN &&
                   (long)eval_view(op1) + (long)eval_view(op2) <= INT_MAX;
    }
}

lemma void lemma_eval_view_bounds(expr_view ev);
    requires is_safe_to_eval(ev) == true;
    ensures INT_MIN <= eval_view(ev) && eval_view(ev) <= INT_MAX;

predicate expression(struct expression *e; expr_view ev) =
    e != 0 &*&
    malloc_block_expression(e) &*&
    e->tag |-> ?tag &*&
    (
        tag == 0 ?
            e->value |-> ?v &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            ev == lit(v)
        : tag == 1 ?
            e->value |-> _ &*&
            e->operand_neg |-> ?op_neg &*&
            e->operand1 |-> _ &*&
            e->operand2 |-> _ &*&
            expression(op_neg, ?ev_neg) &*&
            ev == neg(ev_neg)
        : tag == 2 ?
            e->value |-> _ &*&
            e->operand_neg |-> _ &*&
            e->operand1 |-> ?op1 &*&
            e->operand2 |-> ?op2 &*&
            expression(op1, ?ev1) &*&
            expression(op2, ?ev2) &*&
            ev == add(ev1, ev2)
        :
            false
    );

lemma void lemma_eval_view_bounds(expr_view ev)
    requires is_safe_to_eval(ev) == true;
    ensures INT_MIN <= eval_view(ev) && eval_view(ev) <= INT_MAX;
{
    switch(ev) {
        case lit(v):
        case neg(op):
            lemma_eval_view_bounds(op);
        case add(op1, op2):
            lemma_eval_view_bounds(op1);
            lemma_eval_view_bounds(op2);
    }
}

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


/***
 * Description:
The create_literal function allocates an expression with the tag for literal (0) and value as given.

@param value: the value of this literal expression.

It makes sure that the return value is an exoression of literal with its value set.
*/
struct expression *create_literal(int value)
    //@ requires true;
    //@ ensures expression(result, lit(value));
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    //@ close expression(literal, lit(value));
    return literal;
}


/***
 * Description:
The create_negation function allocates an negated expression for the given expression as an operand.

@param operand: the given expression as an operand to be negated.

It makes sure that the value of returned expression is the negation of the value in the operand.
*/
struct expression *create_negation(struct expression *operand)
    //@ requires expression(operand, ?ev);
    //@ ensures expression(result, neg(ev));
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    //@ close expression(negation, neg(ev));
    return negation;
}


/***
 * Description:
The create_addition function allocates an expression that adds two given expressions as operands.

@param operand1 and operand2: the two given expression as an operands to be added.

It makes sure that the value of returned expression is the sum of value of two given expressions.
*/
struct expression *create_addition(struct expression *operand1, struct expression *operand2)
    //@ requires expression(operand1, ?ev1) &*& expression(operand2, ?ev2);
    //@ ensures expression(result, add(ev1, ev2));
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    //@ close expression(addition, add(ev1, ev2));
    return addition;
}


/***
 * Description:
The evaluate function calculates the value of an given expression recursively and return the such value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
    //@ requires expression(expression, ?ev) &*& is_safe_to_eval(ev) == true;
    //@ ensures expression(expression, ev) &*& result == eval_view(ev);
{
    //@ open expression(expression, ev);
    int result = 0;
    int tag = expression->tag;
    if (tag == 0) {
        //@ switch(ev) { case lit(v): default: }
        result = expression->value;
    } else if (tag == 1) {
        //@ switch(ev) { case neg(op): default: }
        int v = evaluate(expression->operand_neg);
        //@ lemma_eval_view_bounds(op);
        //@ produce_limits(v);
        if (v < 0 - INT_MAX) {abort();}
        result = 0 - v;
    } else {
        //@ switch(ev) { case add(op1, op2): default: }
        int v1 = evaluate(expression->operand1);
        int v2 = evaluate(expression->operand2);
        //@ lemma_eval_view_bounds(op1);
        //@ produce_limits(v1);
        //@ lemma_eval_view_bounds(op2);
        //@ produce_limits(v2);
        if ((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
            || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1)) { abort();}
        result = v1 + v2;
    }
    //@ close expression(expression, ev);
    return result;
}


/***
 * Description:
The dispose_expression function frees the memory allocated for the expression and its components.

@param expression: the current expression to be disposed.
*/
void dispose_expression(struct expression *expression)
    //@ requires expression(expression, _);
    //@ ensures true;
{
    //@ open expression(expression, _);
    int tag = expression->tag;
    if (tag == 0) {
        free(expression);
    } else if (tag == 1) {
        dispose_expression(expression->operand_neg);
        free(expression);
    } else {
        dispose_expression(expression->operand1);
        dispose_expression(expression->operand2);
        free(expression);
    }
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the operations of expression. 
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    // Build 1 + -(5 + 3);
    void *e1_v = create_literal(1);
    void *e2_v = create_literal(5);
    void *e3_v = create_literal(3);
    void *e4_v = create_addition(e2_v, e3_v);
    void *e5_v = create_negation(e4_v);
    void *e6_v = create_addition(e1_v, e5_v);
    
    //@ struct expression *e6 = e6_v;
    //@ expr_view ev6 = add(lit(1), neg(add(lit(5), lit(3))));
    //@ assert expression(e6, ev6);
    
    // Prove safety and value for evaluation
    //@ expr_view ev4 = add(lit(5), lit(3));
    //@ assert eval_view(ev4) == 8;
    //@ assert is_safe_to_eval(lit(5)) == true;
    //@ assert is_safe_to_eval(lit(3)) == true;
    //@ assert is_safe_to_eval(ev4) == true;
    
    //@ expr_view ev5 = neg(ev4);
    //@ assert eval_view(ev5) == -8;
    //@ assert is_safe_to_eval(ev5) == true;
    
    //@ assert is_safe_to_eval(lit(1)) == true;
    //@ assert is_safe_to_eval(ev6) == true;
    //@ assert eval_view(ev6) == -7;
    
    int value = evaluate(e6_v);
    assert(value == 0 - 7);
    
    dispose_expression(e6_v);
    return 0;
}