#include "stdlib.h"

/*@
// A predicate family to represent ownership of the data stored in the stack.
// It is indexed by the destructor function pointer.
predicate_family data_pred(destructor* p)(void* data);
@*/
  

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

/*@
// A predicate for a linked list of nodes.
// 'n' is the head of the list.
// 'd' is the destructor for the data in each node.
// 'vs' is a ghost list of the data pointers.
predicate nodes(struct node* n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_pred(d)(data) &*&
        nodes(next, d, ?rest_vs) &*&
        vs == cons(data, rest_vs);
@*/

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

/*@
// A predicate for the stack data structure.
// 's' is the stack pointer.
// 'd' is the destructor.
// 'vs' is a ghost list of the data pointers.
predicate stack(struct stack* s, destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    is_destructor(d) == true &*&
    nodes(first, d, vs);
@*/


/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};


/*
  Destructors
*/


/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
//@ requires data_pred(this)(data);
//@ ensures emp;



// TODO: make this function pass the verification
/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, ?d, ?vs);
    //@ ensures emp;
{
    //@ open stack(stack, d, vs);
    struct node* current = stack->first;
    destructor* destructor = stack->destructor;
  
    while (current != 0)
        //@ invariant nodes(current, destructor, ?current_vs) &*& is_destructor(destructor) == true;
    {
        //@ open nodes(current, destructor, current_vs);
        struct node* next = current->next;
        destructor(current->data);
        free(current);
        current = next;
    }
    //@ open nodes(current, destructor, _); // current is 0, so this consumes nodes(0, d, nil)
    free(stack);
}