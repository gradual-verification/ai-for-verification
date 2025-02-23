#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*equals() function
-params: void* v1, void* v2
-description: compare two void pointers*/
typedef bool equals(void* v1, void* v2);

/*create_list() function
-params: none
-description: create a new list*/
struct node* create_list() 
{
  return 0;
}

/*add() function
-params: struct node* n, void* v
-description: add a new element to the list*/
struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}

/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list contains the element*/
bool list_contains(struct node* n, void* v, equals* eq) 
{
  if(n == 0) {
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      return cont;
    }
  }
}

/*my_equals() function
-params: void* v1, void* v2
-description: compare two void pointers*/
bool my_equals(void* v1, void* v2) //@: equals
{
  if((uintptr_t)v1 == (uintptr_t)v2) {
    return true;
  } else {
    return false;
  }
  
}

/*test_contains()
-params: none
-description: test if the list
contains the element*/
void test_contains() 
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 2, my_equals);
  assert(cont == true);
}

/*test_does_not_contain()
-params: none
-description: test if the list 
does not contain the element*/
void test_does_not_contain() 
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 4, my_equals);
  assert(cont == false);
}


