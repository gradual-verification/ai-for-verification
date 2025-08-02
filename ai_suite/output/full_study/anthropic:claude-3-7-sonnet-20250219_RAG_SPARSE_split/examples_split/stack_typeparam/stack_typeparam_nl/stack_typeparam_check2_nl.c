#include "stdlib.h"
  

/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

/*@
  predicate node(struct node* n; void* data, struct node* next) =
    n->data |-> data &*& n->next |-> next &*& malloc_block_node(n);
    
  predicate nodes(struct node* first; list<void*> datas) =
    first == 0 ?
      datas == nil
    :
      first != 0 &*& node(first, ?data, ?next) &*& nodes(next, ?rest) &*& datas == cons(data, rest);
      
  predicate stack(struct stack* s; list<void*> datas) =
    s->first |-> ?first &*& s->destructor |-> ?destructor &*& s->size |-> ?size &*&
    malloc_block_stack(s) &*& nodes(first, datas) &*& is_destructor(destructor) == true &*&
    size == length(datas);
@*/

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
  predicate data(struct data* d; int foo, int bar) =
    d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);
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
//@ requires exists<void*>(?p) &*& p == data;
//@ ensures emp;


/* create_empty_stack function
-params: A destructor
This function makes sure to create and return an empty stack */
struct stack* create_empty_stack(destructor* destructor)
//@ requires is_destructor(destructor) == true;
//@ ensures stack(result, nil);
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close nodes(0, nil);
  //@ close stack(stack, nil);
  return stack;
}


/* destroy_stack function
-params: A stack
This function makes sure to destroy the stack by destructing the data of each node and freeing each node. */
void destroy_stack(struct stack* stack)
//@ requires stack(stack, ?datas);
//@ ensures emp;
{
  //@ open stack(stack, datas);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  //@ open nodes(current, datas);
  while ( current != 0 )
    /*@ invariant exists<destructor*>(?d) &*& d == destructor &*& is_destructor(d) == true &*&
                 exists<struct node*>(?c) &*& c == current &*& 
                 nodes(c, ?remaining) &*& c != 0 ? true : remaining == nil; @*/
  {
    //@ open nodes(current, remaining);
    struct node* next = current->next;
    //@ open node(current, ?data, next);
    //@ close exists(data);
    destructor(current->data);
    free(current);
    current = next;
    //@ if (current != 0) { open nodes(current, ?tail); close nodes(current, tail); }
  }
  free(stack);
}


/* push function
-params: A stack and a data element, where the data has ownership
This function makes sure to push the data element onto the head of stack (with ownership) */
void push(struct stack* stack, void* data)
//@ requires stack(stack, ?datas) &*& exists<void*>(?p) &*& p == data &*& stack->size < INT_MAX;
//@ ensures stack(stack, cons(data, datas));
{
  //@ open stack(stack, datas);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
  
  //@ close node(node, data, stack->first);
  //@ open nodes(stack->first, datas);
  //@ close nodes(node, cons(data, datas));
  //@ close stack(stack, cons(data, datas));
}


/* pop function
-params: A stack
-description: Pops the top element from the stack.
It requires that the stack is not empty.
It ensures that the head element is removed and returned (with ownership) */
void* pop(struct stack* stack)
//@ requires stack(stack, ?datas) &*& datas != nil &*& stack->size > INT_MIN;
//@ ensures stack(stack, tail(datas)) &*& exists<void*>(?p) &*& p == result &*& result == head(datas);
{
  //@ open stack(stack, datas);
  struct node* first = stack->first;
  //@ open nodes(first, datas);
  //@ open node(first, ?data, ?next);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  
  //@ close exists(data);
  //@ close stack(stack, tail(datas));
  return data;
}


/*
  create_data function
  - params: two integers foo and bar
  - description: This function creates a data structure and initializes its fields by the fiven foo and bar.
*/
struct data* create_data(int foo, int bar)
//@ requires true;
//@ ensures data(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  
  //@ close data(data, foo, bar);
  return data;
}


/*
  destroy_data function
  - params: data stucture
  - description: This function frees the memory allocated for the data.
*/
void destroy_data(struct data* data) //@ : destructor
//@ requires data(data, _, _);
//@ ensures emp;
{
  //@ open data(data, _, _);
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
  
  //@ close exists(d1);
  push(stack, d1);
  //@ close exists(d2);
  push(stack, d2);

  struct data* d = pop(stack);
  //@ open exists<void*>(?p1);
  //@ assert p1 == d;
  //@ open data(d, _, _);
  //@ close data(d, _, _);
  destroy_data(d);

  d = pop(stack);
  //@ open exists<void*>(?p2);
  //@ assert p2 == d;
  //@ open data(d, _, _);
  //@ close data(d, _, _);
  destroy_data(d);
  
  destroy_stack(stack);
}