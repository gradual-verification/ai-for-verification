#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);

/*@

predicate nodes(struct node* n; list<void*> vs) =
  n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

@*/

/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list() 
  //@ requires true;
  //@ ensures nodes(result, nil);
{
  return 0;
  //@ close nodes(0, nil);
}

/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v) 
  //@ requires nodes(n, ?vs);
  //@ ensures nodes(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  //@ close nodes(nn, cons(v, vs));
  return nn;
}

/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
  //@ requires nodes(n, ?vs) &*& is_equals(eq) == true;
  //@ ensures nodes(n, vs) &*& result == mem(v, vs);
{
  //@ open nodes(n, vs);
  if(n == 0) {
    //@ close nodes(0, nil);
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close nodes(n, vs);
      return true;
    } else {
      bool result = list_contains(n->next, v, eq);
      //@ close nodes(n, vs);
      return result;
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
  return (uintptr_t)v1 == (uintptr_t)v2;
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
  //@ open nodes(n, _);
}