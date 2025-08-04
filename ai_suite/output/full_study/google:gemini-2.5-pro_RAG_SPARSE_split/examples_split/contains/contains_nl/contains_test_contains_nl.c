#include "stdlib.h"
#include "assert.h"
#include <stdint.h>

/*@

// A predicate for a linked list of void pointers.
// It maps a C list pointer 'n' to a ghost list of values 'vs'.
predicate list(struct node *n, list<void*> vs) =
    n == 0 ?
        // If the C pointer is null, the ghost list is empty.
        vs == nil
    :
        // If the C pointer is not null, it must point to a valid node.
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        // The rest of the list is described recursively.
        list(next, ?tail) &*&
        // The ghost list is built by prepending the current value.
        vs == cons(v, tail);

@*/

struct node {
  void* value;
  struct node* next;
};


/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);
    //@ requires true;
    //@ ensures result == (v1 == v2);


/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
  //@ close list(0, nil);
  return 0;
}


/*add() function
-params: struct node* n, void* v
-description: add a new element to the list.
It requires that n is the starting node of the list.
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v)
    //@ requires list(n, ?vs);
    //@ ensures list(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close list(nn, cons(v, vs));
  return nn;
}


/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list.
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq)
    //@ requires list(n, ?vs) &*& is_equals(eq) == true;
    //@ ensures list(n, vs) &*& result == mem(v, vs);
{
  //@ open list(n, vs);
  if(n == 0) {
    //@ close list(0, nil);
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      //@ close list(n, vs);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close list(n, vs);
      return cont;
    }
  }
}


/*my_equals() function
-params: void* v1, void* v2
-description: checks whether two pointers have an equal value.
*/
bool my_equals(void* v1, void* v2) //@ : equals
    //@ requires true;
    //@ ensures result == (v1 == v2);
{
  if((uintptr_t)v1 == (uintptr_t)v2) {
    return true;
  } else {
    return false;
  }
}


// TODO: make this function pass the verification
/*test_contains()
-params: none
-description: test if the list
contains the element*/
void test_contains()
    //@ requires true;
    //@ ensures true;
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 2, my_equals);
  assert(cont == true);
  
  // The list is leaked, which is allowed by the 'ensures true' contract.
  // To clean up memory, a dispose function would be needed.
}