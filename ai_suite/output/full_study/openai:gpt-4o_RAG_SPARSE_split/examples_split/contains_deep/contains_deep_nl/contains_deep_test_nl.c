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

/*@
predicate nodes(struct node* n; list<void*> vs) =
  n == 0 ? vs == nil :
  n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
  nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate list(struct node* n; list<void*> vs) =
  nodes(n, vs);
@*/

/*create_list() function
-params: none
-description: creates an empty list*/
struct node* create_list() 
  //@ requires true;
  //@ ensures list(result, nil);
{
  return 0;
  //@ close list(0, nil);
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
  //@ close nodes(nn, cons(v, vs));
  //@ close list(nn, cons(v, vs));
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
      //@ close list(n, vs);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close list(n, vs);
      return cont;
    }
  }
}

/*create_cell() function
-params: an integer
-description: creates a cell with the given value*/
struct cell* create_cell(int v)
  //@ requires true;
  //@ ensures result->val |-> v &*& malloc_block_cell(result);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  //@ close result->val |-> v &*& malloc_block_cell(result);
  return c;
}

/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
  //@ requires x1->val |-> ?v1 &*& x2->val |-> ?v2 &*& malloc_block_cell(x1) &*& malloc_block_cell(x2);
  //@ ensures x1->val |-> v1 &*& x2->val |-> v2 &*& malloc_block_cell(x1) &*& malloc_block_cell(x2) &*& result == (v1 == v2);
{
  return x1->val == x2->val;
}

// TODO: make this function pass the verification
/*test() function
-params: none
-decription: tests the functionality of contain.
*/
void test() 
  //@ requires true;
  //@ ensures true;
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
  //@ assert cont == true;
}