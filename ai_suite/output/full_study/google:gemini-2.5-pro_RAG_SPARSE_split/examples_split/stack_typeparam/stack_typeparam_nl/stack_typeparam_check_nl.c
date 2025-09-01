#include "stdlib.h"
#include "assert.h"
#include "limits.h"
  
/*@
// A predicate family to specify the precondition of a generic destructor function.
// It is indexed by the function pointer of the destructor.
predicate_family destructor_pre(void* func)(void* data);

// The 'destructor' function type, with its contract.
typedef void destructor(void* data);
    requires destructor_pre(this)(data);
    ensures true;
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
// A recursive predicate for a linked list of nodes.
// It is parameterized by the list of data pointers and the destructor.
// The destructor's contract determines the predicate for the data.
predicate nodes(struct node *n, list<void*> vs, destructor* dtor) =
    n == 0 ?
        vs == nil
    :
        n->data |-> ?d &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        destructor_pre(dtor)(d) &*&
        nodes(next, ?tail, dtor) &*&
        vs == cons(d, tail);

// A predicate for the stack structure.
// It is parameterized by the destructor and the list of data pointers.
predicate stack(struct stack *s; destructor* dtor, list<void*> vs) =
    s->first |-> ?f &*&
    s->destructor |-> dtor &*&
    s->size |-> length(vs) &*&
    malloc_block_stack(s) &*&
    is_destructor(dtor) == true &*&
    nodes(f, vs, dtor);
@*/


/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

/*@
predicate data_struct(struct data *d; int foo, int bar) =
    d->foo |-> foo &*&
    d->bar |-> bar &*&
    malloc_block_data(d);

// An instance of the destructor_pre family for the specific destroy_data function.
// It states that to destroy a 'data' object, one must have ownership of it.
predicate_family_instance destructor_pre(destroy_data)(void* d) =
    data_struct((struct data*)d, _, _);
@*/


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
  
  //@ close nodes(0, nil, destructor);
  //@ close stack(stack, destructor, nil);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
    //@ requires stack(stack, ?dtor, ?vs);
    //@ ensures true;
{
  //@ open stack(stack, dtor, vs);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant nodes(current, ?rem_vs, dtor);
  {
    //@ open nodes(current, rem_vs, dtor);
    struct node* next = current->next;
    void* data = current->data;
    destructor(data);
    free(current);
    current = next;
  }
  //@ open nodes(0, _, _);
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
    //@ requires stack(stack, ?dtor, ?vs) &*& destructor_pre(dtor)(data) &*& length(vs) < INT_MAX;
    //@ ensures stack(stack, dtor, cons(data, vs));
{
  //@ open stack(stack, dtor, vs);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  
  //@ close nodes(node, cons(data, vs), dtor);
  
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();
  }
  stack->size++;
  
  //@ close stack(stack, dtor, cons(data, vs));
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
    //@ requires stack(stack, ?dtor, ?vs) &*& vs != nil;
    //@ ensures stack(stack, dtor, tail(vs)) &*& destructor_pre(dtor)(result);
{
  //@ open stack(stack, dtor, vs);
  //@ open nodes(stack->first, vs, dtor);
  struct node* first = stack->first;
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


/* size function
-params: A stack
This function makes sure to return the size of the stack and does not modify the stack. */
int size(struct stack* stack)
    //@ requires [?f]stack(stack, ?dtor, ?vs);
    //@ ensures [f]stack(stack, dtor, vs) &*& result == length(vs);
{
  //@ open [f]stack(stack, dtor, vs);
  int size = stack->size;
  //@ close [f]stack(stack, dtor, vs);
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


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(void* data) //@ : destructor
    //@ requires destructor_pre(destroy_data)(data);
    //@ ensures true;
{
  //@ open destructor_pre(destroy_data)(data);
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
  struct stack* stack = create_empty_stack(destroy_data);
  int s = size(stack);
  assert(s == 0);
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  assert(s == 2);
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}