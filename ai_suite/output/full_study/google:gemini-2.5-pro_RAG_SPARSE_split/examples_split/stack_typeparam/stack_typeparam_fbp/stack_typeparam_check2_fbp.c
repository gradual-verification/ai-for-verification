#include "stdlib.h"
  

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

inductive Stack<T> =
  | Nil
  | Cons(void* data, T info, Stack<T>);

predicate Node<T>(predicate(void *, T) Ownership, struct node* node, void *data, T info, struct node* next) =
  malloc_block_node( node ) &*&
  node->data |-> data &*&
  node->next |-> next &*&
  Ownership(data, info) &*&
  node != 0;

predicate StackItems<T>(predicate(void *, T) Ownership, struct node* head, Stack<T> S) =
  head == 0 ? S == Nil :
  Node(Ownership, head, ?data, ?info, ?next) &*&
  StackItems(Ownership, next, ?T) &*&
  S == Cons(data, info, T);

predicate Stack<T>(struct stack* stack, destructor* destructor, predicate(void *, T) Ownership, Stack<T> S) =
  malloc_block_stack(stack) &*&
  [_]is_destructor(destructor, Ownership) &*&
  stack->destructor |-> destructor &*&
  stack->first |-> ?first &*&
  stack->size |-> ?size &*&
  size == Size(S) &*&
  StackItems(Ownership, first, S);

fixpoint Stack<T> Push<T>(void* item, T info, Stack<T> Stack)
{
  return Cons(item, info, Stack);
}

fixpoint Stack<T> Pop<T>(Stack<T> Stack)
{
  switch ( Stack )
  {
    case Nil:
      return Nil;

    case Cons(x, y, T):
      return T;
  }
}

fixpoint bool IsEmpty<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return true;
    
    case Cons(x, y, T):
      return false;
  }
}

fixpoint int Size<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return 0;
    
    case Cons(x, y, T):
      return 1 + Size(T);
  }
}
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

predicate Data(struct data* data, int foo, int bar) =
  malloc_block_data(data) &*&
  data->foo |-> foo &*&
  data->bar |-> bar;

@*/

/*@

inductive DataCarrier =
  | DataCarrier(int, int);

fixpoint int GetFoo(DataCarrier dc)
{
  switch ( dc )
  {
    case DataCarrier(x, y):
      return x;
  }
}

fixpoint int GetBar(DataCarrier dc)
{
  switch ( dc )
  {
    case DataCarrier(x, y):
      return y;
  }
}

predicate Data_Ownership(struct data *data, DataCarrier DC) = Data(data, GetFoo(DC), GetBar(DC));

@*/

/*
  Destructors
*/


typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
  //@ ensures true;


struct stack* create_empty_stack/*@ <T> @*/(destructor* destructor)
  //@ requires [_]is_destructor<T>(destructor, ?Ownership);
  //@ ensures Stack(result, destructor, Ownership, ?Stack) &*& IsEmpty(Stack) == true;
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  //@ close StackItems(Ownership, 0, Nil);
  //@ close Stack(result, destructor, Ownership, Nil);
  return stack;
}


void destroy_stack/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?S);
  //@ ensures true;
{
  //@ open Stack(stack, destructor, Ownership, S);
  //@ open StackItems(Ownership, ?first, S);
  struct node* current = stack->first;
  
  while ( current != 0 )
    //@ invariant StackItems(Ownership, current, ?S_current);
  {
    //@ open StackItems(Ownership, current, S_current);
    //@ open Node(Ownership, current, ?data, ?info, ?next_node);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
    //@ S_current is Cons(data, info, _);
  }
  //@ open StackItems(0, _, _);
  free(stack);
}


void push/*@ <T> @*/(struct stack* stack, void* data)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?S) &*& Ownership(data, ?info);
  //@ ensures Stack(stack, destructor, Ownership, Push(data, info, S));
{
  //@ open Stack(stack, destructor, Ownership, S);
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();
  }
  stack->size++;
  //@ close Stack(stack, destructor, Ownership, Push(data, info, S));
}


void* pop/*@ <T> @*/(struct stack* stack)
  /*@
  requires Stack<T>(stack, ?destructor, ?Ownership, Cons(?head, ?info, ?tail));
  @*/
  /*@
  ensures Stack(stack, destructor, Ownership, tail) &*&
          Ownership(head, info) &*& result == head;
  @*/
{
  //@ open Stack(stack, destructor, Ownership, Cons(head, info, tail));
  //@ open StackItems(Ownership, ?first, Cons(head, info, tail));
  //@ open Node(Ownership, first, head, info, ?next);
  struct node* first_node = stack->first;
  void* data = first_node->data;
  stack->first = first_node->next;
  free(first_node);
  if (stack->size == INT_MIN) {
    abort();
  }
  stack->size--;
  //@ close Stack(stack, destructor, Ownership, tail);
  return data;
}


struct data* create_data(int foo, int bar)
  //@ requires true;
  //@ ensures Data(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close Data(data, foo, bar);
  return data;
}



void destroy_data(struct data* data)
  //@ : destructor<DataCarrier>(Data_Ownership)
  //@ requires Data_Ownership(data, _);
  //@ ensures true;
{
  //@ open Data_Ownership(data, _);
  //@ open Data(data, _, _);
  free(data);
}


// TODO: make this function pass the verification
void check2()
  //@ requires true;
  //@ ensures true;
{
  struct stack* stack = create_empty_stack<DataCarrier>(destroy_data);
  struct data* d1 = create_data(1, 1);
  //@ close Data_Ownership(d1, DataCarrier(1, 1));
  struct data* d2 = create_data(2, 2);
  //@ close Data_Ownership(d2, DataCarrier(2, 2));
  
  push(stack, d1);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  
  destroy_data(d);
  
  destroy_stack(stack);
}