#include "stdlib.h"
#include "assert.h"
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

/*@
predicate data_struct(struct data* p; int foo, int bar) =
    p->foo |-> foo &*& p->bar |-> bar &*& malloc_block_data(p);
@*/


/*
  Destructors
*/

/*@
predicate_family data_pred(destructor* d)(void* data);
@*/

/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
//@ requires data_pred(this)(data);
//@ ensures true;

/*@
predicate nodes(struct node* n, list<void*> vs, destructor* d) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?data &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        data_pred(d)(data) &*&
        nodes(next, ?rest, d) &*& vs == cons(data, rest);

predicate stack(struct stack* s, list<void*> vs, destructor* d) =
    s->first |-> ?first &*& s->destructor |-> d &*& s->size |-> ?size &*&
    malloc_block_stack(s) &*&
    is_destructor(d) == true &*&
    nodes(first, vs, d) &*&
    size == length(vs);
@*/


/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
    //@ requires is_destructor(destructor) == true;
    //@ ensures stack(result, nil, destructor);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, nil, destructor);
  //@ close stack(stack, nil, destructor);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, ?vs, ?d);
    //@ ensures true;
{
  //@ open stack(stack, vs, d);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current, ?current_vs, d) &*& is_destructor(d) == true;
  {
    //@ open nodes(current, current_vs, d);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  //@ open nodes(0, _, d);
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
    //@ requires stack(stack, ?vs, ?d) &*& data_pred(d)(data) &*& length(vs) < INT_MAX;
    //@ ensures stack(stack, cons(data, vs), d);
{
  //@ open stack(stack, vs, d);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  //@ close nodes(node, cons(data, vs), d);
  //@ close stack(stack, cons(data, vs), d);
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?vs, ?d) &*& vs != nil;
    //@ ensures stack(stack, tail(vs), d) &*& result == head(vs) &*& data_pred(d)(result);
{
  //@ open stack(stack, vs, d);
  struct node* first = stack->first;
  //@ open nodes(first, vs, d);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  //@ close stack(stack, tail(vs), d);
  return data;
}


/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
    //@ requires [?f]stack(stack, ?vs, ?d);
    //@ ensures [f]stack(stack, vs, d) &*& result == length(vs);
{
  //@ open [f]stack(stack, vs, d);
  int size = stack->size;
  //@ close [f]stack(stack, vs, d);
  return size;
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

/*@
predicate_family_instance data_pred(destroy_data)(void* data) =
    data_struct((struct data*)data, _, _);
@*/

/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
    //@ requires data_pred(destroy_data)(data);
    //@ ensures true;
{
  //@ open data_pred(destroy_data)(data);
  free(data);
}


// TODO: make this function pass the verification
/*
  check function
  - params: none
  - description: This function creates a stack, pushes two data elements onto it, 
    and checks the size of the stack.
*/
void check()
    //@ requires true;
    //@ ensures true;
{
  //@ is_destructor_t(destroy_data);
  struct stack* stack = create_empty_stack(destroy_data);
  int s = size(stack);
  assert(s == 0);
  
  struct data* data = create_data(1, 2);
  //@ close data_pred(destroy_data)(data);
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  //@ close data_pred(destroy_data)(data);
  push(stack, data);

  s = size(stack);
  assert(s == 2);
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}