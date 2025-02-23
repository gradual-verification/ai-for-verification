#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

typedef bool equals(void* x1, void* x2);

/*create_list() function
-params: none
-description: creates an empty list*/
struct node* create_list() 
{
  return 0;
}

/*add() function
-params: a node pointer and a void pointer
-description: adds a value to the list*/
struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}

/*list_contains() function
-params: a node pointer, a void pointer, and an equals function pointer
-description: checks if the given value is in the list*/
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
-description: compares the values of the two cells*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
{
  
  return x1->val == x2->val;

}

/*test() function
-params: none
-decription: creates and uses a list*/
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
