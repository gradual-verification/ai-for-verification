#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// Predicate to describe the state of a node
/*@
predicate node(struct node* n; void* value, struct node* next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);
@*/

// Predicate to describe the state of a list of nodes
/*@
predicate nodes(struct node* n; list<void*> values) =
    n == 0 ? values == nil : node(n, ?value, ?next) &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/

// Predicate for the equals function
/*@
predicate_family equals_predicate(void* p)(void* v1, void* v2) =
    is_equals(p) == true;
@*/

// equals() function
//-params: void* v1, void* v2
//-description: checks whether two pointers are equal. It doesn't have a concrete definition.
typedef bool equals(void* v1, void* v2);
//@ requires equals_predicate(this)(v1, v2);
//@ ensures equals_predicate(this)(v1, v2) &*& result == (v1 == v2);

// Example usage of equals
bool example_equals(void* v1, void* v2) //@ : equals
//@ requires equals_predicate(example_equals)(v1, v2);
//@ ensures equals_predicate(example_equals)(v1, v2) &*& result == (v1 == v2);
{
    return v1 == v2;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct node* n1 = malloc(sizeof(struct node));
    struct node* n2 = malloc(sizeof(struct node));
    if (n1 == 0 || n2 == 0) abort();
    n1->value = (void*)1;
    n1->next = 0;
    n2->value = (void*)1;
    n2->next = 0;
    //@ close node(n1, (void*)1, 0);
    //@ close node(n2, (void*)1, 0);
    //@ close nodes(n1, cons((void*)1, nil));
    //@ close nodes(n2, cons((void*)1, nil));
    //@ close equals_predicate(example_equals)(n1, n2);
    bool result = example_equals(n1, n2);
    //@ open equals_predicate(example_equals)(n1, n2);
    //@ open nodes(n1, _);
    //@ open nodes(n2, _);
    free(n1);
    free(n2);
    return 0;
}