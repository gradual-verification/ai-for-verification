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

/*@
// A predicate family to represent the memory/ownership that a given
// destructor function is responsible for. It is indexed by the
// function pointer itself.
predicate_family destructor_pre(void* d)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires destructor_pre(this)(data);
    //@ ensures true;

/*@
// A recursive predicate to model the linked list of nodes.
// It holds a ghost list `vs` of the data pointers.
predicate nodes(struct node *n; list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next, ?rest) &*&
        vs == cons(data, rest);

// The main predicate for the stack.
// It owns the stack struct, the nodes, and the preconditions
// for the destructor of each element in the stack.
predicate stack(struct stack *s; list<void*> vs, destructor *d) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(first, vs) &*&
    is_destructor(d) == true &*&
    foreach(vs, destructor_pre(d));
@*/


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?vs, ?d) &*& vs != nil;
    //@ ensures stack(stack, tail(vs), d) &*& destructor_pre(d)(head(vs));
{
    //@ open stack(stack, vs, d);
    struct node* first = stack->first;
    //@ open nodes(first, vs);
    void* data = first->data;
    stack->first = first->next;
    free(first);
    if (stack->size == INT_MIN) {
        abort();
    }
    stack->size--;
    //@ foreach_remove(head(vs), vs);
    //@ close stack(stack, tail(vs), d);
    return data;
}


/* get_destructor function
-params: A stack

It makes sure to return the destructor of the stack*/
destructor* get_destructor(struct stack* stack)
    //@ requires [?f]stack(stack, ?vs, ?d);
    //@ ensures [f]stack(stack, vs, d) &*& result == d;
{
    //@ open stack(stack, vs, d);
    destructor* d = stack->destructor;
    //@ close stack(stack, vs, d);
    return d;
}


// TODO: make this function pass the verification
/* pop_destroy function
-params: A stack
It makes sure to pop the top element from the stack and destroys it*/
void pop_destroy(struct stack* stack)
    //@ requires stack(stack, ?vs, ?d) &*& vs != nil;
    //@ ensures stack(stack, tail(vs), d);
{
    void* data = pop(stack);
    destructor* d = get_destructor(stack);
    d(data);
}