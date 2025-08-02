#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
// Define a predicate for a linked list
predicate nodes(struct node* n; list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*& values == cons(v, values0);

// Define a predicate for an empty list
predicate empty_list(struct node* n) =
    n == 0;
@*/

// create_list() function
// -params: none
// -description: creates an empty list
struct node* create_list() 
//@ requires true;
//@ ensures empty_list(result) &*& nodes(result, nil);
{
  return 0;
  //@ close nodes(0, nil);
  //@ close empty_list(0);
}