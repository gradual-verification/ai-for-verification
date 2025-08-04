#include "stdlib.h"

/*@
// A predicate for a generic linked list of void pointers.
predicate nodes(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?tail) &*& vs == cons(v, tail);

// Predicate family for the data pointed to by the list's value pointers.
// The family is indexed by the 'equals' function pointer, allowing different
// equality functions to have different data requirements.
predicate_family value_pred(void* eq)(void* p);

// A logical (ghost) function that corresponds to the 'equals' C function.
// It defines the logical meaning of equality for the given function 'eq'.
fixpoint bool are_equal(void* eq, void* p1, void* p2);

// A logical (ghost) function that corresponds to the 'list_contains' C function.
// It recursively checks for membership in a ghost list using the logical 'are_equal' function.
fixpoint bool list_contains_fp(list<void*> vs, void* v, void* eq) {
    switch (vs) {
        case nil: return false;
        case cons(h, t): return are_equal(eq, v, h) || list_contains_fp(t, v, eq);
    }
}
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
/*@
    requires value_pred(this)(x1) &*& value_pred(this)(x2);
    ensures value_pred(this)(x1) &*& value_pred(this)(x2) &*& result == are_equal(this, x1, x2);
@*/


// TODO: make this function pass the verification
/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, 
which can be applied on the value of v and each element in the list. 
It ensures that the list is unchanged, and the return value is the result 
of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq)
    //@ requires nodes(n, ?vs) &*& is_equals(eq) == true &*& value_pred(eq)(v) &*& foreach(vs, value_pred(eq));
    //@ ensures nodes(n, vs) &*& value_pred(eq)(v) &*& foreach(vs, value_pred(eq)) &*& result == list_contains_fp(vs, v, eq);
{
  //@ open nodes(n, vs);
  if(n == 0) {
    //@ open foreach(nil, _);
    //@ close foreach(nil, value_pred(eq));
    return false;
  } else {
    //@ open foreach(vs, value_pred(eq));
    //@ assert vs == cons(?h, ?t);
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close nodes(n, vs);
      //@ close foreach(vs, value_pred(eq));
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close nodes(n, vs);
      //@ close foreach(vs, value_pred(eq));
      return cont;
    }
  }
}