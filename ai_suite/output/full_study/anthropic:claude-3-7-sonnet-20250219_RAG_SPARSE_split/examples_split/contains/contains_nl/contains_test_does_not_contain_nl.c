#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*@
// Define a predicate for a linked list of nodes
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

/*@
// Define a predicate family for the equals function
predicate_family equals_data(void* equals_func)(void* v1, void* v2);
@*/

/*create_list() function
-params: none
-description: return an empty list. */
struct node* create_list() 
//@ requires true;
//@ ensures nodes(result, nil);
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


/*@
// Lemma to help with the verification of list_contains
lemma void list_contains_lemma(struct node* n, void* v, equals* eq, list<void*> values)
  requires nodes(n, values) &*& is_equals(eq) == true;
  ensures nodes(n, values) &*& is_equals(eq) == true &*&
          (list_contains(n, v, eq) == true ? 
            (exists<int>(?idx) &*& 0 <= idx &*& idx < length(values) &*& eq(v, nth(idx, values)) == true) : 
            (forall<int>((i) => 0 <= i && i < length(values) ? eq(v, nth(i, values)) == false : true)));
{
  open nodes(n, values);
  if (n == 0) {
    close nodes(n, values);
  } else {
    void* head_value = n->value;
    struct node* next = n->next;
    list<void*> tail = tail(values);
    
    if (eq(v, head_value)) {
      // If the value matches the head, we found it
      //@ close exists(0);
    } else {
      // Otherwise, recursively check the rest of the list
      list_contains_lemma(next, v, eq, tail);
      
      // If it's in the tail, adjust the index
      if (list_contains(next, v, eq)) {
        //@ open exists(?idx);
        //@ close exists(idx + 1);
      }
    }
    close nodes(n, values);
  }
}
@*/

/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
//@ requires nodes(n, ?values) &*& is_equals(eq) == true;
//@ ensures nodes(n, values) &*& is_equals(eq) == true &*& result == (exists<int>(?idx) &*& 0 <= idx &*& idx < length(values) &*& eq(v, nth(idx, values)) == true);
{
  //@ list_contains_lemma(n, v, eq, values);
  if(n == 0) {
    return false;
  } else {
    //@ open nodes(n, values);
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      //@ close nodes(n, values);
      //@ close exists(0);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close nodes(n, values);
      if (cont) {
        //@ open exists(?idx);
        //@ close exists(idx + 1);
      }
      return cont;
    }
  }
}


/*my_equals() function
-params: void* v1, void* v2
-description: checks whether two pointers have an equal value.
*/
/*@
predicate_family_instance equals_data(my_equals)(void* v1, void* v2) =
  true;
@*/

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
  
  /*@
  // Prove that the list contains [3, 2, 1]
  assert nodes(n, cons((void*)3, cons((void*)2, cons((void*)1, nil))));
  @*/
  
  bool cont = list_contains(n, (void*) 4, my_equals);
  
  /*@
  // Prove that my_equals((void*)4, (void*)3) == false
  assert my_equals((void*)4, (void*)3) == false;
  // Prove that my_equals((void*)4, (void*)2) == false
  assert my_equals((void*)4, (void*)2) == false;
  // Prove that my_equals((void*)4, (void*)1) == false
  assert my_equals((void*)4, (void*)1) == false;
  
  // Therefore, (void*)4 is not in the list
  assert cont == false;
  @*/
  
  assert(cont == false);
}