#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);

//@ predicate nodes(struct node* n; list<void*> vs) = n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

//@ predicate list_contains_pre(struct node* n, void* v, equals* eq) = nodes(n, ?vs) &*& is_equals(eq) == true;
//@ predicate list_contains_post(struct node* n, void* v, equals* eq, bool result) = nodes(n, ?vs) &*& is_equals(eq) == true &*& result == mem(v, vs);

bool list_contains(struct node* n, void* v, equals* eq) 
  //@ requires list_contains_pre(n, v, eq);
  //@ ensures list_contains_post(n, v, eq, result);
{
  //@ open list_contains_pre(n, v, eq);
  if(n == 0) {
    //@ close list_contains_post(n, v, eq, false);
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close list_contains_post(n, v, eq, true);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close list_contains_post(n, v, eq, cont);
      return cont;
    }
  }
}