#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
predicate nodes(struct node* n, list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?nxt &*& nodes(nxt, ?vs2) &*& vs == cons(v, vs2);
@*/

// TODO: make this function pass the verification
struct node* create_list() 
  //@ requires true;
  //@ ensures nodes(result, nil);
{
  return 0;
}