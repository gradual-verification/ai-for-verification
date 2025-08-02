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
// Predicate for a cell structure
predicate cell(struct cell* c, int value) =
  c->val |-> value &*& malloc_block_cell(c);

// Predicate for a linked list node
predicate node(struct node* n, void* v, struct node* next) =
  n->value |-> v &*& n->next |-> next &*& malloc_block_node(n);

// Predicate for a linked list
predicate nodes(struct node* n; list<void*> values) =
  n == 0 ?
    values == nil
  :
    node(n, ?v, ?next) &*& nodes(next, ?tail_values) &*& values == cons(v, tail_values);

// Predicate family for equals function
predicate_family equals_data(void* equals_func)(void* x1, void* x2);

// Predicate family instance for cell_equals
predicate_family_instance equals_data(cell_equals)(void* x1, void* x2) =
  cell((struct cell*)x1, ?v1) &*& cell((struct cell*)x2, ?v2) &*& v1 == v2;
@*/

/*create_list() function
-params: none
-description: creates an empty list*/
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
  //@ close node(nn, v, n);
  //@ close nodes(nn, cons(v, values));
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
//@ requires nodes(n, ?values) &*& is_equals(eq) == true;
//@ ensures nodes(n, values) &*& result == exists(values, (contains_value)(v, eq));
{
  //@ open nodes(n, values);
  if(n == 0) {
    //@ close nodes(n, values);
    return false;
  } else {
    //@ open node(n, ?head_value, ?next);
    bool cont = eq(v, n->value);
    if(cont) {
      //@ close node(n, head_value, next);
      //@ close nodes(n, values);
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      //@ close node(n, head_value, next);
      //@ close nodes(n, values);
      return cont;
    }
  }
}

/*@
// Helper fixpoint to check if a value is contained in the list
fixpoint bool contains_value(void* v, equals* eq)(void* x) {
  return eq(v, x) == true;
}
@*/

/*create_cell() function
-params: an integer
-description: creates a cell with the given value*/
struct cell* create_cell(int v)
//@ requires true;
//@ ensures cell(result, v);
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  //@ close cell(c, v);
  return c;
}


/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@ : equals
//@ requires cell(x1, ?v1) &*& cell(x2, ?v2);
//@ ensures cell(x1, v1) &*& cell(x2, v2) &*& result == (v1 == v2);
{
  //@ open cell(x1, v1);
  //@ open cell(x2, v2);
  bool result = x1->val == x2->val;
  //@ close cell(x1, v1);
  //@ close cell(x2, v2);
  return result;
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
  
  //@ close equals_data(cell_equals)(c4, c3);
  //@ close equals_data(cell_equals)(c4, c2);
  //@ close equals_data(cell_equals)(c4, c1);
  
  bool cont = list_contains(n, c4, cell_equals);
  
  // Free all allocated memory to avoid memory leaks
  //@ open nodes(n, _);
  //@ open node(n, _, ?next1);
  //@ open cell(c3, _);
  free(n);
  
  //@ open nodes(next1, _);
  //@ open node(next1, _, ?next2);
  //@ open cell(c2, _);
  free(next1);
  
  //@ open nodes(next2, _);
  //@ open node(next2, _, ?next3);
  //@ open cell(c1, _);
  free(next2);
  
  //@ open nodes(next3, _);
  //@ open cell(c4, _);
  free(c4);
}