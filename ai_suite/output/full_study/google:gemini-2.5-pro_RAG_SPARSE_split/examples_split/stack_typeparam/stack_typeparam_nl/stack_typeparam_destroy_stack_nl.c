#include "stdlib.h"
  
/*
  Destructors
*/

/*@
// A predicate family to represent the ownership of the generic data.
// The family is indexed by the destructor function pointer.
predicate_family data_inv(destructor* p)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
/*@
    requires data_inv(this)(data);
    ensures true;
@*/


/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*@
// A predicate for the linked list of nodes.
// It is parameterized by the destructor 'd' to handle the generic data.
// It is recursively defined on the 'n' parameter.
// 'vs' is a ghost list of the data pointers for functional correctness.
predicate nodes(struct node* n; destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_inv(d)(data) &*&
        nodes(next; d, ?tail_vs) &*&
        vs == cons(data, tail_vs);

// A predicate for the stack structure.
// It ties together the stack's fields, the nodes, and the destructor contract.
predicate stack(struct stack* s; destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    is_destructor(d) == true &*&
    nodes(first; d, vs);
@*/

/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};




// TODO: make this function pass the verification
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, ?d, ?vs);
    //@ ensures true;
{
  //@ open stack(stack, d, vs);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current; d, ?rem_vs) &*& is_destructor(d) == true;
  {
    //@ open nodes(current; d, rem_vs);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(current; d, _);
  free(stack);
}