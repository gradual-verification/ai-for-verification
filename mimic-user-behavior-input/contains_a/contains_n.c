#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


typedef bool equals(void* v1, void* v2);

/* Description
  - Behavior: This function creates an empty linked list.
*/
struct node* create_list() 
{
  return 0;
}

/* Description
  - Behavior: This function adds a new element to the beginning of a linked list.
  - Parameters:
    - `n`: Pointer to the head of the current linked list.
    - `v`: Pointer to the value to be added.
*/
struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}

/* Description
  - Behavior: This function checks if a value is present in the linked list.
  - Parameters:
    - `n`: Pointer to the head of the linked list to be searched.
    - `v`: Pointer to the value to be searched for.
    - `eq`: Pointer to a function that determines equality between two values.
*/
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

/* Description: 
  - Behavior: Custom equality function used for comparing values.
  - Parameters:
    - `v1`: Pointer to the first value to be compared.
    - `v2`: Pointer to the second value to be compared.
*/
bool my_equals(void* v1, void* v2) //@: equals
{
  if(v1 == v2) {
    return true;
  } else {
    return false;
  }
  
}

/* Description: 
  - Behavior: test list_contains works as expected or not for contains situation.
*/
void test_contains() 
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 2, my_equals);
  assert(cont == true);
}

/* Description: 
  - Behavior: test list_contains works as expected or not for not contain situation.
*/
void test_does_not_contain() 
{
  struct node* n = create_list();
  n = add(n, (void*) 1);
  n = add(n, (void*) 2);
  n = add(n, (void*) 3);
  bool cont = list_contains(n, (void*) 4, my_equals);
  assert(cont == false);
}


