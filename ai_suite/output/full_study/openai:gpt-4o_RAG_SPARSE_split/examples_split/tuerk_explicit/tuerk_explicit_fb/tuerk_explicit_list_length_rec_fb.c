#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(value, values0);

@*/

// TODO: make this function pass the verification
int list_length_rec(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    if (node == 0) {
        return 0;
    } else {
        //@ open nodes(node, values);
        int length0 = list_length_rec(node->next);
        //@ close nodes(node->next, _);
        //@ close nodes(node, values);
        return 1 + length0;
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *n3 = malloc(sizeof(struct node));
    if (n3 == 0) { abort(); }
    n3->value = 3;
    n3->next = 0;
    //@ close nodes(n3, cons(3, nil));

    struct node *n2 = malloc(sizeof(struct node));
    if (n2 == 0) { abort(); }
    n2->value = 2;
    n2->next = n3;
    //@ close nodes(n2, cons(2, cons(3, nil)));

    struct node *n1 = malloc(sizeof(struct node));
    if (n1 == 0) { abort(); }
    n1->value = 1;
    n1->next = n2;
    //@ close nodes(n1, cons(1, cons(2, cons(3, nil))));

    int length = list_length_rec(n1);
    //@ assert length == 3;

    free(n1);
    free(n2);
    free(n3);

    return 0;
}