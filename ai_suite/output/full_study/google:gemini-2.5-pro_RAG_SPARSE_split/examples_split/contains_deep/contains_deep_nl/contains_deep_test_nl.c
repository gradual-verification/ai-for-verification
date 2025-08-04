#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
// A predicate representing a `struct cell` in memory.
predicate cell(struct cell* c; int v) =
    c->val |-> v &*& malloc_block_cell(c);

// A predicate representing a generic linked list.
// It models the list as a ghost list of void pointers.
predicate nodes(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(v, rest);

// A predicate family to specify the behavior of an `equals` function.
// It relates a generic pointer `p` to an abstract integer value `v`.
predicate_family eq_spec(equals* eq)(void* p, int v);

// A recursive predicate that builds a ghost list of abstract integer values (`abs_vs`)
// from a list of concrete void pointers (`ps`), using a given `equals` function.
predicate build_abs_list(list<void*> ps, equals* eq, list<int> abs_vs) =
    switch(ps) {
        case nil: return abs_vs == nil;
        case cons(h, t):
            return
                eq_spec(eq)(h, ?h_abs) &*&
                build_abs_list(t, eq, ?t_abs) &*&
                abs_vs == cons(h_abs, t_abs);
    };

// An instance of the `eq_spec` family for the `cell_equals` function.
// It specifies that the abstract value of a cell pointer is the integer it contains.
predicate_family_instance eq_spec(cell_equals)(void* p, int v) =
    cell((struct cell*)p, v);

@*/

/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);
    //@ requires is_equals(this) == true &*& eq_spec(this)(x1, ?v1) &*& eq_spec(this)(x2, ?v2);
    //@ ensures eq_spec(this)(x1, v1) &*& eq_spec(this)(x2, v2) &*& result == (v1 == v2);


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
    //@ requires nodes(n, ?vs) &*& pointer_within_limits(v) == true;
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

It requires that n is the starting node of the list, eq is a equal function,
which can be applied on the value of v and each element in the list.
It ensures that the list is unchanged, and the return value is the result
of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq)
    //@ requires is_equals(eq) == true &*& nodes(n, ?vs) &*& eq_spec(eq)(v, ?v_abs) &*& build_abs_list(vs, eq, ?abs_vs);
    //@ ensures nodes(n, vs) &*& eq_spec(eq)(v, v_abs) &*& build_abs_list(vs, eq, abs_vs) &*& result == mem(v_abs, abs_vs);
{
    //@ open nodes(n, vs);
    //@ open build_abs_list(vs, eq, abs_vs);
    if(n == 0) {
        //@ close nodes(0, nil);
        //@ close build_abs_list(nil, eq, nil);
        return false;
    } else {
        bool cont = eq(v, n->value);
        if(cont) {
            //@ close build_abs_list(vs, eq, abs_vs);
            //@ close nodes(n, vs);
            return true;
        } else {
            cont = list_contains(n->next, v, eq);
            //@ close build_abs_list(vs, eq, abs_vs);
            //@ close nodes(n, vs);
            return cont;
        }
    }
}



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
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
    //@ requires eq_spec(cell_equals)(x1, ?v1) &*& eq_spec(cell_equals)(x2, ?v2);
    //@ ensures eq_spec(cell_equals)(x1, v1) &*& eq_spec(cell_equals)(x2, v2) &*& result == (v1 == v2);
{
  //@ open cell(x1, v1);
  //@ open cell(x2, v2);
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
  //@ close nodes(n, nil);

  struct cell* c1 = create_cell(1);
  n = add(n, c1);

  struct cell* c2 = create_cell(2);
  n = add(n, c2);

  struct cell* c3 = create_cell(3);
  n = add(n, c3);

  struct cell* c4 = create_cell(3);

  //@ list<void*> vs = cons(c3, cons(c2, cons(c1, nil)));
  //@ list<int> abs_vs = cons(3, cons(2, cons(1, nil)));

  // Establish the precondition for list_contains by building the abstract list predicate.
  //@ close build_abs_list(nil, cell_equals, nil);
  //@ close build_abs_list(cons(c1, nil), cell_equals, cons(1, nil));
  //@ close build_abs_list(cons(c2, cons(c1, nil)), cell_equals, cons(2, cons(1, nil)));
  //@ close build_abs_list(vs, cell_equals, abs_vs);

  bool cont = list_contains(n, c4, cell_equals);

  // From the postcondition of list_contains, we know:
  // cont == mem(3, cons(3, cons(2, cons(1, nil))))
  // which evaluates to true.
  //@ assert cont == true;

  // Clean up ghost predicates to leave the heap state as it was.
  //@ open build_abs_list(vs, cell_equals, abs_vs);
  //@ open build_abs_list(cons(c2, cons(c1, nil)), cell_equals, cons(2, cons(1, nil)));
  //@ open build_abs_list(cons(c1, nil), cell_equals, cons(1, nil));
  //@ open build_abs_list(nil, cell_equals, nil);
}