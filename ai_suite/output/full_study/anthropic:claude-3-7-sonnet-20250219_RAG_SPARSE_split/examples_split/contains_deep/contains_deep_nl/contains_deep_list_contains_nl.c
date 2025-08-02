#include "stdlib.h"

/*@
// Predicate for a linked list node
predicate node_p(struct node *n, void *value, struct node *next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);

// Predicate for a linked list
predicate nodes(struct node *n; list<void *> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?tail_values) &*& values == cons(v, tail_values);

// Predicate for the equals function
predicate equals_p(equals *eq) = is_equals(eq) == true;

// Function contract for equals function type
@*/

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
//@ requires true;
//@ ensures true;

/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, 
which can be applied on the value of v and each element in the list. 
It ensures that the list is unchanged, and the return value is the result 
of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
//@ requires nodes(n, ?values) &*& is_equals(eq) == true;
//@ ensures nodes(n, values) &*& result == contains(v, values, eq);
{
  if(n == 0) {
    //@ open nodes(n, values);
    return false;
  } else {
    //@ open nodes(n, values);
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close nodes(n, values);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close nodes(n, values);
      return cont;
    }
  }
}

/*@
// Fixpoint to check if a value is contained in a list using an equals function
fixpoint bool contains(void *v, list<void *> values, equals *eq) {
    switch (values) {
        case nil: return false;
        case cons(head, tail): 
            return eq(v, head) || contains(v, tail, eq);
    }
}
@*/