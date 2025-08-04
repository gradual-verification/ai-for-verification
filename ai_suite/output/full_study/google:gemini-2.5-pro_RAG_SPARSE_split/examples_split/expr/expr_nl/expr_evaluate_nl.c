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

inductive tree =
    | Lit(int v)
    | Neg(tree t)
    | Add(tree t1, tree t2);

fixpoint int eval_tree(tree t) {
    switch (t) {
        case Lit(v): return v;
        case Neg(t1): return -eval_tree(t1);
        case Add(t1, t2): return eval_tree(t1) + eval_tree(t2);
    }
}

fixpoint bool is_in_range(tree t) {
    switch (t) {
        case Lit(v):
            return INT_MIN <= v && v <= INT_MAX;
        case Neg(t1):
            return is_in_range(t1) && eval_tree(t1) != INT_MIN;
        case Add(t1, t2):
            {
                int v1 = eval_tree(t1);
                int v2 = eval_tree(t2);
                return is_in_range(t1) && is_in_range(t2) &&
                       !((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
                       || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1));
            }
    }
}

predicate expression_pred(struct expression *expr; tree t) =
    expr != 0 &*&
    malloc_block_expression(expr) &*&
    expr->tag |-> ?tag &*&
    (
        tag == 0 ?
            expr->value |-> ?v &*&
            expr->operand_neg |-> _ &*&
            expr->operand1 |-> _ &*&
            expr->operand2 |-> _ &*&
            t == Lit(v)
        : tag == 1 ?
            expr->value |-> _ &*&
            expr->operand_neg |-> ?op_neg &*&
            expr->operand1 |-> _ &*&
            expr->operand2 |-> _ &*&
            expression_pred(op_neg, ?t_neg) &*&
            t == Neg(t_neg)
        : tag == 2 ?
            expr->value |-> _ &*&
            expr->operand_neg |-> _ &*&
            expr->operand1 |-> ?op1 &*&
            expr->operand2 |-> ?op2 &*&
            expression_pred(op1, ?t1) &*&
            expression_pred(op2, ?t2) &*&
            t == Add(t1, t2)
        :
            false
    );

@*/


// TODO: make this function pass the verification
/***
 * Description:
The evaluate function calculates the value of an given expression recursively and return the such value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
    //@ requires expression_pred(expression, ?t);
    //@ ensures is_in_range(t) == true &*& expression_pred(expression, t) &*& result == eval_tree(t);
{
    int result = 0;
    int tag = expression->tag;
    if (tag == 0)
        result = expression->value;
    else if (tag == 1) {
        int v = evaluate(expression->operand_neg);
        if (v < 0 - INT_MAX) {abort();}
        result = 0 - v;
    } else {
        int v1 = evaluate(expression->operand1);
        int v2 = evaluate(expression->operand2);
        if ((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
            || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1)) { abort();}
        result = v1 + v2;
    }
    return result;
}