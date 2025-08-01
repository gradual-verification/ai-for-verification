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


// TODO: make this function pass the verification
/***
 * Description:
The evaluate function calculates the value of an given expression recursively and return the such value.

@param expression: the current expression to be evaluated.
*/
int evaluate(struct expression *expression)
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

