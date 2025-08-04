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

// Forward declaration for use in struct stack
typedef void destructor(void* data);

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

/*@

// Predicate family for the data chunks managed by the generic stack.
// The family is indexed by the destructor function pointer.
predicate_family data_chunk(destructor* d)(void* data);

// Predicate for the concrete data struct used in the example.
predicate data_struct(struct data* d; int foo, int bar) =
    d->foo |-> foo &*&
    d->bar |-> bar &*&
    malloc_block_data(d);

// Predicate for a list of nodes in the stack.
predicate nodes(struct node* n, destructor* d, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        data_chunk(d)(data) &*&
        nodes(next, d, ?rest) &*&
        vs == cons(data, rest);

// Predicate for the stack itself.
predicate stack(struct stack* s; destructor* d, list<void*> vs) =
    s->first |-> ?first &*&
    s->destructor |-> d &*&
    s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    is_destructor(d) == true &*&
    nodes(first, d, vs) &*&
    size == length(vs);

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
    //@ requires data_chunk(this)(data);
    //@ ensures emp;



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
    //@ requires stack(stack, ?d, ?vs);
    //@ ensures emp;
{
  //@ open stack(stack, d, vs);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current, d, ?current_vs) &*& is_destructor(d) == true;
  {
    //@ open nodes(current, d, current_vs);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, d, _);
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
    //@ requires stack(stack, ?d, ?vs) &*& data_chunk(d)(data) &*& length(vs) < INT_MAX;
    //@ ensures stack(stack, d, cons(data, vs));
{
  //@ open stack(stack, d, vs);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, d, cons(data, vs));
  //@ close stack(stack, d, cons(data, vs));
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?d, ?vs) &*& vs != nil;
    //@ ensures stack(stack, d, tail(vs)) &*& data_chunk(d)(result);
{
  //@ open stack(stack, d, vs);
  struct node* first = stack->first;
  //@ open nodes(first, d, vs);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, d, tail(vs));
  return data;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
    //@ requires true;
    //@ ensures data_struct(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close data_struct(data, foo, bar);
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
//@ predicate_family_instance data_chunk(destroy_data)(void* data) = data_struct((struct data*)data, _, _);
void destroy_data(void* data) //@ : destructor
    //@ requires data_chunk(destroy_data)(data);
    //@ ensures emp;
{
  //@ open data_chunk(destroy_data)(data);
  //@ open data_struct((struct data*)data, _, _);
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
  
  //@ close data_chunk(destroy_data)(d1);
  push(stack, d1);
  //@ close data_chunk(destroy_data)(d2);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  
  destroy_data(d);
  
  destroy_stack(stack);
}