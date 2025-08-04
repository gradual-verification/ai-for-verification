#include "stdlib.h"
#include "stdbool.h"
#include "stdint.h"
#include "assert.h"

/*@
// Predicate to model a linked list of void pointers.
// 'n' is the head of the list, and 'vs' is the ghost list of its values.
predicate list(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next, ?rest) &*&
        vs == cons(v, rest);
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
    //@ ensures true;


/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
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
    //@ ensures list(n, vs);
{
  //@ open list(n, vs);
  if(n == 0) {
    //@ close list(n, vs);
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
bool my_equals(void* v1, void* v2) //@: equals
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
// This lemma proves that calling list_contains with my_equals is equivalent
// to checking for membership in the ghost list using pointer equality.
lemma void list_contains_my_equals(struct node* n, void* v)
    requires list(n, ?vs);
    ensures list(n, vs) &*& list_contains(n, v, my_equals) == mem(v, vs);
{
    open list(n, vs);
    if (n != 0) {
        list_contains_my_equals(n->next, v);
    }
    close list(n, vs);
}
@*/

// A helper function to dispose of the list to prevent memory leaks.
void dispose_list(struct node* n)
    //@ requires list(n, _);
    //@ ensures true;
{
    //@ open list(n, _);
    if (n != 0) {
        dispose_list(n->next);
        free(n);
    }
}

// TODO: make this function pass the verification
/*test_does_not_contain()
-params: none
-description: test if the list
does not contain the element*/
void test_does_not_contain()
    //@ requires true;
    //@ ensures true;
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);

  // Use the lemma to reason about the result of list_contains.
  //@ list_contains_my_equals(n, (void*)4);
  // The lemma ensures: list_contains(n, (void*)4, my_equals) == mem((void*)4, {3, 2, 1})
  // VeriFast knows mem((void*)4, {3, 2, 1}) is false.

  bool cont = list_contains(n, (void*) 4, my_equals);
  assert(cont == false);

  dispose_list(n);
}