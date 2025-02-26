#include "stdlib.h"

/*
  Destructors
*/

typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
  //@ ensures emp;
  

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

lemma void RewritePushCons<T>(void* item, T info, Stack<T> Stack)
  requires emp;
  ensures Push(item, info, Stack) == Cons(item, info, Stack);
{
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

lemma void IsEmptyNil<T>(Stack<T> S)
  requires emp;
  ensures IsEmpty(S) ? S == Nil : emp;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
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

lemma void SizeEmptyStack<T>(Stack<T> S)
  requires emp;
  ensures IsEmpty(S) ? Size(S) == 0 : true;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

lemma void SizePush<T>(void* data, T info, Stack<T> S)
  requires emp;
  ensures Size( Push(data, info, S) ) == Size(S) + 1;
{
  switch ( S )
  {
    case Nil:
    case Cons(x, y, z):
  }
}


fixpoint void* GetTopPointer<T>(Stack<T> S)
{
  switch ( S )
  {
    case Nil:
      return 0;

    case Cons(x, y, z):
      return x;
  }  
}

lemma void PushNotNil<T>(void* data, T info, Stack<T> Stack)
  requires emp;
  ensures Push(data, info, Stack) != Nil;
{
  switch ( Stack )
  {
    case Nil:
    case Cons(x, y, z):
  }
}

@*/

struct stack* create_empty_stack/*@ <T> @*/(destructor* destructor)
  //@ requires [_]is_destructor<T>(destructor, ?Ownership);
  //@ ensures Stack(result, destructor, Ownership, ?Stack);
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
  //@ ensures emp;
{
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
  {
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  free(stack);
}

void push/*@ <T> @*/(struct stack* stack, void* data)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Push(data, info, Stack));
{
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();  // or handle error as necessary
  }
  stack->size++;
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
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  return data;
}

destructor* get_destructor/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  /*@
  ensures Stack(stack, destructor, Ownership, Stack) &*&
          [_]is_destructor(result, Ownership) &*&
          result == destructor;
  @*/
{
  destructor* d = stack->destructor;
  return d;
}

void pop_destroy/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Pop(Stack));
{
  void* data = pop(stack);
  destructor* d = get_destructor(stack);
  d(data);
}

bool is_empty/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Stack);
{
  struct node* first = stack->first;
  return first == 0;
}

int size/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack);
  //@ ensures Stack(stack, destructor, Ownership, Stack);
{
  int size = stack->size;
  return size;
}



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

struct data* create_data(int foo, int bar)
  //@ requires emp;
  //@ ensures Data(result, foo, bar);
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}

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

void destroy_data(struct data* data)
  //@ requires Data_Ownership(data, _);
  //@ ensures emp;
{
  free(data);
}

void check()
  //@ requires emp;
  //@ ensures emp;
{
  struct stack* stack = create_empty_stack(destroy_data);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}

void check2()
  //@ requires emp;
  //@ ensures emp;
{
  struct stack* stack = create_empty_stack(destroy_data);
  struct data* d1 = create_data(1, 1);
  struct data* d2 = create_data(2, 2);
  
  push(stack, d1);
  push(stack, d2);

  struct data* d = pop(stack);
  destroy_data(d);

  d = pop(stack);
  
  destroy_data(d);
  
  destroy_stack(stack);
}

/*@

lemma void CheckPushPop<T>(void* item, T info, Stack<T> S)
  requires emp;
  ensures Pop( Push( item, info, S ) ) == S;
{
}

lemma void CheckSizePush<T>(void* item, T info, Stack<T> S)
  requires emp;
  ensures Size( Push( item, info, S ) ) == 1 + Size( S );
{
}

@*/
