#include "stdlib.h"
#include "limits.h"

/*@
// Predicate family to hold ownership of the data pointed to by stack elements.
// It is indexed by the destructor function pointer.
predicate_family data_resource(void* destructor)(void* data);
@*/
  
/*
  Destructors
*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
/*@
    requires data_resource(this)(data);
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
// Predicate for a linked list of nodes.
// It holds ownership of the nodes and the data they point to (via data_resource).
predicate nodes(struct node* n, destructor* dtor, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        (dtor == 0 ? true : data_resource(dtor)(d)) &*&
        nodes(next, dtor, ?rest) &*&
        vs == cons(d, rest);

// Predicate for a stack.
// It holds ownership of the stack struct and the list of nodes.
predicate stack(struct stack* s, destructor* dtor, list<void*> vs) =
    s->first |-> ?f &*&
    s->destructor |-> dtor &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    nodes(f, dtor, vs) &*&
    (dtor == 0 ? true : is_destructor(dtor) == true);
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
/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?dtor, ?vs) &*& vs != nil;
    //@ ensures stack(stack, dtor, tail(vs)) &*& result == head(vs) &*& (dtor == 0 ? true : data_resource(dtor)(head(vs)));
{
  //@ open stack(stack, dtor, vs);
  struct node* first = stack->first;
  //@ open nodes(first, dtor, vs);
  
  void* data = first->data;
  stack->first = first->next;
  
  free(first);
  
  if (stack->size == INT_MIN) {
    abort();
  }
  stack->size--;
  
  //@ close stack(stack, dtor, tail(vs));
  return data;
}