

struct expression {
    int tag;
    int value;
    struct expression *operand_neg;
    struct expression *operand1;
    struct expression *operand2;
};


struct expression *create_literal(int value)
{
    struct expression *literal = malloc(sizeof(struct expression));
    if (literal == 0) abort();
    literal->tag = 0;
    literal->value = value;
    return literal;
}


struct expression *create_negation(struct expression *operand)
{
    struct expression *negation = malloc(sizeof(struct expression));
    if (negation == 0) abort();
    negation->tag = 1;
    negation->operand_neg = operand;
    return negation;
}


struct expression *create_addition(struct expression *operand1, struct expression *operand2)
{
    struct expression *addition = malloc(sizeof(struct expression));
    if (addition == 0) abort();
    addition->tag = 2;
    addition->operand1 = operand1;
    addition->operand2 = operand2;
    return addition;
}


int evaluate(struct expression *expression)
{
    int result = 0;
    int tag = expression->tag;
    if (tag == 0) {
        result = expression->value;
    } else if (tag == 1) {
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


void dispose_expression(struct expression *expression)
{
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


int main()
{
    void *e1_v = create_literal(1);
    void *e2_v = create_literal(5);
    void *e3_v = create_literal(3);
    void *e4_v = create_addition(e2_v, e3_v);
    void *e5_v = create_negation(e4_v);
    void *e6_v = create_addition(e1_v, e5_v);
    
    
    
    
    
    int value = evaluate(e6_v);
    assert(value == 0 - 7);
    
    dispose_expression(e6_v);
    return 0;
}
