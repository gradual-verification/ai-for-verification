#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
predicate list(struct node *n; list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next, ?tail_values) &*&
        values == cons(v, tail_values);
@*/


// TODO: make this function pass the verification
/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
  return 0;
}