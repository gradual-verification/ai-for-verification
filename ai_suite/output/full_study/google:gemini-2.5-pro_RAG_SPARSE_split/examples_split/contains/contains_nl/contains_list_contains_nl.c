#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
// A standard predicate for a singly-linked list segment.
predicate list(struct node *n, list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next, ?tail) &*&
        values == cons(v, tail);

// A predicate family to abstractly specify the behavior of an 'equals' function.
// Any implementation of 'equals' must produce an instance of this predicate,
// relating its inputs to its boolean result.
predicate_family equals_post(equals* p)(void* v1, void* v2, bool result);
@*/


/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);
    //@ requires true;
    //@ ensures equals_post(this)(v1, v2, result);

/*@
// A recursive predicate that defines the post-condition of list_contains.
// It consumes the 'equals_post' chunks for each element in the list and
// defines the final result.
predicate list_contains_post(list<void*> values, void* v, equals* eq, bool result) =
    values == nil ?
        result == false
    :
        equals_post(eq)(v, head(values), ?res_h) &*&
        list_contains_post(tail(values), v, eq, ?res_t) &*&
        result == (res_h || res_t);
@*/

// TODO: make this function pass the verification
/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq)
    //@ requires list(n, ?values) &*& is_equals(eq) == true;
    //@ ensures list_contains_post(values, v, eq, result) &*& list(n, values);
{
  if(n == 0) {
    //@ open list(n, values);
    //@ close list_contains_post(nil, v, eq, false);
    //@ close list(n, values);
    return false;
  } else {
    //@ open list(n, values);
    bool cont = eq(v, n->value);
    //@ assert equals_post(eq)(v, n->value, cont);
    if(cont) {
      list_contains(n->next, v, eq);
      //@ assert list_contains_post(tail(values), v, eq, _);
      //@ close list_contains_post(values, v, eq, true);
      //@ close list(n, values);
      return true;
    } else {
      bool cont_rec = list_contains(n->next, v, eq);
      //@ assert list_contains_post(tail(values), v, eq, cont_rec);
      //@ close list_contains_post(values, v, eq, cont_rec);
      //@ close list(n, values);
      return cont_rec;
    }
  }
}