#include "stdlib.h"
#include "limits.h"
  

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
//@ requires data_inv(this)(data);
//@ ensures true;

/*@

// A predicate family to abstractly represent ownership of the data stored in the stack.
// It is indexed by the destructor function pointer, allowing different data types
// with different destructors to be handled generically.
predicate_family data_inv(destructor* d)(void* data);

// A recursive predicate representing a linked list of nodes.
// It holds ownership of the nodes and the data they point to via `data_inv`.
predicate nodes(struct node* n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_inv(d)(data) &*&
        nodes(next, d, ?rest) &*&
        vs == cons(data, rest);

// The main predicate for the stack data structure.
// It ties together the stack struct, the destructor, and the logical list of elements.
predicate stack(struct stack* s; destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> ?size &*&
    size == length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(first, d, vs);

@*/


// TODO: make this function pass the verification
/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?d, ?vs) &*& vs != nil;
    //@ ensures stack(stack, d, tail(vs)) &*& result == head(vs) &*& data_inv(d)(head(vs));
{
    //@ open stack(stack, d, vs);
    struct node* first = stack->first;
    //@ open nodes(first, d, vs);
    void* data = first->data;
    stack->first = first->next;
    free(first);
    
    // The precondition `vs != nil` implies `length(vs) > 0`.
    // Since `stack->size == length(vs)`, we have `stack->size > 0`.
    // Therefore, `stack->size` cannot be `INT_MIN`, and this check will not abort.
    if (stack->size == INT_MIN) {
        abort();
    }
    stack->size--;
    
    //@ close stack(stack, d, tail(vs));
    return data;
}