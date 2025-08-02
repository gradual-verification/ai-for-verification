#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

// TODO: make this function pass the verification
typedef bool equals(void* x1, void* x2);
    //@ requires true;
    //@ ensures true;

/*@

predicate nodes(struct node *node, list<void*> values) =
    node == 0 ? values == nil : node->value |-> ?value &*& node->next |-> ?next &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(value, values0);

@*/

bool equals_impl(void* x1, void* x2) //@ : equals
    //@ requires true;
    //@ ensures true;
{
    return x1 == x2;
}

bool list_equals(struct node *n1, struct node *n2, equals *eq)
    //@ requires nodes(n1, ?xs1) &*& nodes(n2, ?xs2) &*& is_equals(eq) == true;
    //@ ensures nodes(n1, xs1) &*& nodes(n2, xs2) &*& result ? xs1 == xs2 : xs1 != xs2;
{
    //@ open nodes(n1, xs1);
    //@ open nodes(n2, xs2);
    if (n1 == 0) {
        return n2 == 0;
    } else if (n2 == 0) {
        return false;
    } else {
        if (!eq(n1->value, n2->value)) {
            return false;
        }
        return list_equals(n1->next, n2->next, eq);
    }
    //@ close nodes(n1, xs1);
    //@ close nodes(n2, xs2);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *n1 = malloc(sizeof(struct node));
    struct node *n2 = malloc(sizeof(struct node));
    if (n1 == 0 || n2 == 0) abort();
    n1->value = (void *)1;
    n1->next = 0;
    n2->value = (void *)1;
    n2->next = 0;
    //@ close nodes(n1, cons((void *)1, nil));
    //@ close nodes(n2, cons((void *)1, nil));
    bool result = list_equals(n1, n2, equals_impl);
    //@ open nodes(n1, _);
    //@ open nodes(n2, _);
    free(n1);
    free(n2);
    return 0;
}