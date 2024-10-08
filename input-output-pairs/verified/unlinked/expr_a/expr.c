#include "stdlib.h"

struct literal {
    int tag;
    int value;
};

struct negation {
    int tag;
    void *operand;
};

struct addition {
    int tag;
    void *operand1;
    void *operand2;
};

//TODO: need to fix the error below:
/*@
predicate expression(void *expr, int value) =
    integer(expr, ?tag) &*&
    tag == 0 ? literal_value(expr, value) &*& malloc_block_literal(expr) :
    tag == 1 ? negation_operand(expr, ?operand) &*& malloc_block_negation(expr) &*& expression(operand, ?operandValue) &*& value == 0 - operandValue :
    tag == 2
    &*& addition_operand1(expr, ?operand1) &*& addition_operand2(expr, ?operand2) &*& malloc_block_addition(expr)
    &*& expression(operand1, ?value1) &*& expression(operand2, ?value2) &*& value == value1 + value2;

lemma void same_address_for_literal(void *literal);
    requires malloc_block_literal(literal);
    ensures malloc_block_literal(literal) &*& &(((struct literal *)literal)->tag) == literal;

lemma void same_address_for_negation(void *negation);
    requires malloc_block_negation(negation);
    ensures malloc_block_negation(negation) &*& &(((struct negation *)negation)->tag) == negation;

lemma void same_address_for_addition(void *addition);
    requires malloc_block_addition(addition);
    ensures malloc_block_addition(addition) &*& &(((struct addition *)addition)->tag) == addition;
@*/

struct literal *create_literal(int value)
    //@ requires true;
    //@ ensures expression(result, value);
{
    struct literal *literal = malloc(sizeof(struct literal));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    //@ open literal_tag(literal, 0);
    //@ same_address_for_literal(literal);
    //@ close expression(literal, value);
    return literal;
}

struct negation *create_negation(void *operand)
    //@ requires expression(operand, ?operandValue);
    //@ ensures expression(result, 0 - operandValue);
{
    struct negation *negation = malloc(sizeof(struct negation));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand = operand;
    //@ open negation_tag(negation, 1);
    //@ same_address_for_negation(negation);
    //@ close expression(negation, 0 - operandValue);
    return negation;
}

struct addition *create_addition(void *operand1, void *operand2)
    //@ requires expression(operand1, ?value1) &*& expression(operand2, ?value2);
    //@ ensures expression(result, value1 + value2);
{
    struct addition *addition = malloc(sizeof(struct addition));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    //@ open addition_tag(addition, 2);
    //@ same_address_for_addition(addition);
    //@ close expression(addition, value1 + value2);
    return addition;
}

int evaluate(void *expression)
    //@ requires expression(expression, ?value);
    //@ ensures expression(expression, value) &*& result == value;
{
    //@ open expression(expression, value);
    int result = 0;
    int tag = *((int *)expression);
    if (tag == 0)
        result = ((struct literal *)expression)->value;
    else if (tag == 1) {
        int v = evaluate(((struct negation *)expression)->operand);
        if (v < 0 - INT_MAX) {abort();}
        result = 0 - v;
    } else {
        struct addition *addition = expression;
        int v1 = evaluate(addition->operand1);
        int v2 = evaluate(addition->operand2);
    if ((v2 > 0 && v1 > INT_MAX - v2) || (v1 > 0 && v2 > INT_MAX - v1)
            || (v2 < 0 && v1 < INT_MIN - v2) || (v1 < 0 && v2 < INT_MIN - v1)) { abort();}
        result = v1 + v2;
    }
    //@ close expression(expression, value);
    return result;
}

void dispose_expression(void *expression)
    //@ requires expression(expression, _);
    //@ ensures true;
{
    //@ open expression(expression, _);
    int tag = *((int *)expression);
    if (tag == 0) {
        //@ same_address_for_literal(expression);
        //@ close literal_tag(expression, 0);
        free((struct literal *)expression);
    } else if (tag == 1) {
        struct negation *negation = expression;
        dispose_expression(negation->operand);
        //@ same_address_for_negation(expression);
        //@ close negation_tag(expression, 1);
        free(negation);
    } else {
        struct addition *addition = expression;
        dispose_expression(addition->operand1);
        dispose_expression(addition->operand2);
        //@ same_address_for_addition(expression);
        //@ close addition_tag(expression, 2);
        free(addition);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    // Build 1 + -(5 + 3);
    void *e1 = create_literal(1);
    void *e2 = create_literal(5);
    void *e3 = create_literal(3);
    void *e4 = create_addition(e2, e3);
    void *e5 = create_negation(e4);
    void *e6 = create_addition(e1, e5);
    
    int value = evaluate(e6);
    assert(value == 0 - 7);
    
    dispose_expression(e6);
    return 0;
}