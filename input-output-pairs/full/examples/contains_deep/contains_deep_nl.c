#include "stdlib.h"

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
It ensures that the list is unchanged, and the return value is the result 
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
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
{
  
  return x1->val == x2->val;

}

/*test() function
-params: none
-decription: tests the functionality of contain.
*/
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
