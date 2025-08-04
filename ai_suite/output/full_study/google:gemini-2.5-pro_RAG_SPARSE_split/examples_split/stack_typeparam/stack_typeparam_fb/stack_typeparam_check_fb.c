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
  node->data |-> data &*&
  node->next |-> next &*&
  malloc_block_node(node) &*&
  Ownership(data, info);

predicate StackItems<T>(predicate(void *, T) Ownership, struct node* head, Stack<T> S) =
  head == 0 ? S == Nil :
  Node(Ownership, head, ?data, ?info, ?next) &*&
  StackItems(Ownership, next, ?T) &*&
  S == Cons(data, info, T);

predicate Stack<T>(struct stack* stack, destructor* destructor, predicate(void *, T) Ownership, Stack<T> S) =
  [_]is_destructor(destructor, Ownership) &*&
  stack->destructor |-> destructor &*&
  stack->first |-> ?first &*&
  stack->size |-> ?size &*&
  malloc_block_stack(stack) &*&
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
  data->foo |-> foo &*&
  data->bar |-> bar &*&
  malloc_block_data(data);

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

predicate Data_Ownership(void *data, DataCarrier DC) = 
  Data((struct data*)data, GetFoo(DC), GetBar(DC));

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
  
  return stack;
}


void destroy_stack/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, _, _, ?S);
  //@ ensures true;
{
  destructor* destructor = stack->destructor;
  //@ open Stack<T>(stack, destructor, ?Ownership, S);
  struct node* current = stack->first;
  
  //@ open StackItems<T>(Ownership, current, S);
  while ( current != 0 )
    //@ invariant StackItems<T>(Ownership, current, ?rem_S) &*& [_]is_destructor(destructor, Ownership);
  {
    //@ open StackItems<T>(Ownership, current, rem_S);
    //@ open Node<T>(Ownership, current, ?d, ?i, ?n);
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  
  free(stack);
}


void push/*@ <T> @*/(struct stack* stack, void* data)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack) &*& Ownership(data, ?info);
  //@ ensures Stack(stack, destructor, Ownership, Push(data, info, Stack));
{
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  //@ open Stack<T>(stack, destructor, Ownership, Stack);
  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();
  }
  stack->size++;
  //@ close Node<T>(Ownership, node, data, info, node->next);
  //@ close StackItems<T>(Ownership, node, Push(data, info, Stack));
  //@ close Stack<T>(stack, destructor, Ownership, Push(data, info, Stack));
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
  //@ open Stack<T>(stack, destructor, Ownership, Cons(head, info, tail));
  //@ open StackItems<T>(Ownership, stack->first, Cons(head, info, tail));
  struct node* first = stack->first;
  //@ open Node<T>(Ownership, first, head, info, first->next);
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();
  }
  stack->size--;
  //@ close Stack<T>(stack, destructor, Ownership, tail);
  return data;
}


int size/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Stack) &*& result == Size(Stack);
{
  int size = stack->size;
  return size;
}



struct data* create_data(int foo, int bar)
  //@ requires true;
  //@ ensures Data(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}


void destroy_data(void* data)
  //@ requires Data_Ownership(data, _);
  //@ ensures true;
{
  //@ open Data_Ownership(data, _);
  //@ open Data((struct data*)data, _, _);
  free(data);
}


// TODO: make this function pass the verification
void check()
  //@ requires true;
  //@ ensures true;
{
  struct stack* stack = create_empty_stack<DataCarrier>(destroy_data);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  //@ close Data_Ownership(data, DataCarrier(1, 2));
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  //@ close Data_Ownership(data, DataCarrier(2, 3));
  push(stack, data);

  s = size(stack);
  assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}