#include "stdlib.h"

/*@
// Predicate for the data structure
predicate data_pred(struct data *d; int foo, int bar) =
    d->foo |-> foo &*&
    d->bar |-> bar &*&
    malloc_block_data(d);

// A predicate family to represent ownership of data that can be destroyed
// by a specific destructor function.
predicate_family destructible(void* destructor)(void* data);
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
    //@ requires destructible(this)(data);
    //@ ensures true;


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
// Predicate for a list of nodes, holding ownership of the data via the 'destructible' predicate.
predicate nodes(struct node* n, destructor* destructor, list<void*> elems) =
    n == 0 ?
        elems == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        destructible(destructor)(d) &*&
        nodes(next, destructor, ?rest) &*&
        elems == cons(d, rest);

// Predicate for the stack structure.
predicate stack(struct stack* s; destructor* destructor, list<void*> elems) =
    s->first |-> ?first &*&
    s->destructor |-> destructor &*&
    s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    is_destructor(destructor) == true &*&
    nodes(first, destructor, elems) &*&
    size == length(elems);
@*/


/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};




/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
    //@ requires is_destructor(destructor) == true;
    //@ ensures stack(result, destructor, nil);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, destructor, nil);
  //@ close stack(stack, destructor, nil);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, ?destructor, ?elems);
    //@ ensures true;
{
  //@ open stack(stack, destructor, elems);
  struct node* current = stack->first;
  destructor* dtor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current, dtor, ?current_elems) &*& is_destructor(dtor) == true;
  {
    //@ open nodes(current, dtor, current_elems);
    struct node* next = current->next;
    dtor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, dtor, _);
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
    //@ requires stack(stack, ?destructor, ?elems) &*& destructible(destructor)(data) &*& length(elems) < INT_MAX;
    //@ ensures stack(stack, destructor, cons(data, elems));
{
  //@ open stack(stack, destructor, elems);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  
  //@ close nodes(node, stack->destructor, cons(data, elems));
  
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();
  }
  stack->size++;
  
  //@ close stack(stack, stack->destructor, cons(data, elems));
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?destructor, ?elems) &*& elems != nil;
    //@ ensures stack(stack, destructor, tail(elems)) &*& destructible(destructor)(result) &*& result == head(elems);
{
  //@ open stack(stack, destructor, elems);
  struct node* first = stack->first;
  //@ open nodes(first, destructor, elems);
  
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();
  }
  stack->size--;
  
  //@ close stack(stack, stack->destructor, tail(elems));
  return data;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
    //@ requires true;
    //@ ensures data_pred(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}

/*@
// An instance of the destructible family for the destroy_data function.
// It states that being destructible by 'destroy_data' means holding a 'data_pred' chunk.
predicate_family_instance destructible(destroy_data)(void* data) =
    data_pred((struct data*)data, _, _);
@*/

/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
    //@ requires destructible(destroy_data)(data);
    //@ ensures true;
{
  //@ open destructible(destroy_data)(data);
  free(data);
}


// TODO: make this function pass the verification
/*
  check2 function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    pops and destroys them, and finally destroys the stack.
*/
void check2()
    //@ requires true;
    //@ ensures true;
{
  struct stack* stack = create_empty_stack(destroy_data);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);
  
  //@ close destructible(destroy_data)((void *)d1);
  push(stack, d1);
  //@ close destructible(destroy_data)((void *)d2);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  
  destroy_data(d);
  
  destroy_stack(stack);
}