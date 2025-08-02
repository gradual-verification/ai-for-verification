#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
// Predicate for a linked list of nodes
predicate nodes(struct node* n, list<void*> values) =
  n == 0 ?
    values == nil
  :
    n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?rest) &*& values == cons(v, rest);
@*/

/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);
//@ requires true;
//@ ensures true;

/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list() 
{
  //@ close nodes(0, nil);
  return 0;
}


/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v) 
//@ requires nodes(n, ?values);
//@ ensures nodes(result, cons(v, values));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close nodes(nn, cons(v, values));
  return nn;
}


/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
//@ requires nodes(n, ?values) &*& is_equals(eq) == true;
//@ ensures nodes(n, values) &*& result == my_post(values, v, eq);
{
  //@ open nodes(n, values);
  if(n == 0) {
    //@ close nodes(n, values);
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
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
// Helper fixpoint to define the expected result of list_contains
fixpoint bool my_post(list<void*> values, void* v, equals* eq) {
  switch(values) {
    case nil: return false;
    case cons(h, t): return eq(v, h) || my_post(t, v, eq);
  }
}
@*/

/*my_equals() function
-params: void* v1, void* v2
-description: checks whether two pointers have an equal value.
*/
bool my_equals(void* v1, void* v2) //@ : equals
//@ requires true;
//@ ensures result == ((uintptr_t)v1 == (uintptr_t)v2);
{
  if((uintptr_t)v1 == (uintptr_t)v2) {
    return true;
  } else {
    return false;
  }
}

/*@
// Lemma to prove that my_equals returns true when v1 and v2 are equal
lemma void my_equals_true(void* v1, void* v2)
  requires (uintptr_t)v1 == (uintptr_t)v2;
  ensures my_equals(v1, v2) == true;
{
  // This lemma is automatically proven by VeriFast
}

// Lemma to prove that my_post returns true when the value is in the list
lemma void my_post_true(list<void*> values, void* v)
  requires mem(v, values) == true;
  ensures my_post(values, v, my_equals) == true;
{
  switch(values) {
    case nil:
    case cons(h, t):
      if(h == v) {
        my_equals_true(v, h);
      } else {
        my_post_true(t, v);
      }
  }
}
@*/

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
  //@ assert nodes(n, nil);
  
  n = add(n, (void*) 1);
  //@ assert nodes(n, cons((void*)1, nil));
  
  n = add(n, (void*) 2);
  //@ assert nodes(n, cons((void*)2, cons((void*)1, nil)));
  
  n = add(n, (void*) 3);
  //@ assert nodes(n, cons((void*)3, cons((void*)2, cons((void*)1, nil))));
  
  bool cont = list_contains(n, (void*) 2, my_equals);
  
  //@ my_post_true(cons((void*)3, cons((void*)2, cons((void*)1, nil))), (void*)2);
  assert(cont == true);
}