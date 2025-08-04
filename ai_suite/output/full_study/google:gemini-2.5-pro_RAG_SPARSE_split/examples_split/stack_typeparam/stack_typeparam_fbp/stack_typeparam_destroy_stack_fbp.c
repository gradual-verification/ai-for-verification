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
  StackItems(Ownership, next, ?S_tail) &*&
  S == Cons(data, info, S_tail);

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


// TODO: make this function pass the verification
void destroy_stack/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?dest, ?own, ?S);
  //@ ensures true;
{
  //@ open Stack<T>(stack, dest, own, S);
  struct node* current = stack->first;
  destructor* destructor = stack->destructor;
  
  while ( current != 0 )
    //@ invariant StackItems<T>(own, current, ?S_current);
  {
    //@ open StackItems<T>(own, current, S_current);
    //@ open Node<T>(own, current, ?data, ?info, ?next_node);
    
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  
  //@ open StackItems<T>(own, current, ?S_current); // S_current is Nil here
  free(stack);
}