#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.

It requires that there exists two functions to get the value of the elements of x1 and x2,
and an equal function before calling this function.
It ensures that the values are not changed and equal function still exists after calling this function. 
Its return value is the result of executing the equal function on the parameters.
*/
typedef bool equals(void* x1, void* x2);

/*create_list() function
-params: none
-description: creates an empty list*/
struct node* create_list() 
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

It requires that n is the starting node of the list, eq is a equal function, 
which can be applied on the value of v and each element in the list. 
It ensures that the list and equal function are unchanged, and the return value is the result 
of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
{
  if(n == 0) {
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      return cont;
    }
  }
}

// specific to cell

struct cell {
  int val;
};

/*create_cell() function
-params: an integer
-description: creates a cell with the given value*/
struct cell* create_cell(int v)
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  return c;
}

/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.

It requires that the cells contain the value, and there exists an equal function before calling this function,
It ensures that the cells and equal function are still unchanged after calling this function. 
Its return value is the result of executing the equal function on the parameters.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
{
  
  return x1->val == x2->val;

}

/*test() function
-params: none
-decription: tests the functionality of contain.
It creates and uses a list, and check whether iot contains a cell with a specified value. */
void test() 
{
  struct node* n = create_list();
  struct cell* c1 = create_cell(1);
  n = add(n, c1);
  struct cell* c2 = create_cell(2);
  n = add(n, c2);
  struct cell* c3 = create_cell(3);
  n = add(n, c3);
  struct cell* c4 = create_cell(3);
  bool cont = list_contains(n, c4, cell_equals);
}
