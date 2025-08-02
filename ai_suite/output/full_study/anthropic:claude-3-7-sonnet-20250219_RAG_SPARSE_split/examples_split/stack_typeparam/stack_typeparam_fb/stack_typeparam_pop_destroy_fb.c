#include "stdlib.h"


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

struct node {
  void* data;
  struct node* next;
};

struct stack {
  struct node* first;
  destructor* destructor;
  int size;
};

/*
  Destructors
*/


typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
  //@ ensures true;



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


// TODO: make this function pass the verification
void pop_destroy/*@ <T> @*/(struct stack* stack)
  //@ requires Stack<T>(stack, ?destructor, ?Ownership, ?Stack) &*& Stack != Nil;
  //@ ensures Stack(stack, destructor, Ownership, Pop(Stack));
{
  //@ open Stack(stack, destructor, Ownership, Stack);
  //@ assert stack->first |-> ?first;
  //@ assert StackItems(Ownership, first, Stack);
  //@ open StackItems(Ownership, first, Stack);
  //@ assert first != 0;
  //@ assert Node(Ownership, first, ?data, ?info, ?next);
  //@ assert StackItems(Ownership, next, ?Tail);
  //@ assert Stack == Cons(data, info, Tail);
  
  void* data = pop(stack);
  //@ assert Ownership(data, info);
  
  destructor* d = get_destructor(stack);
  //@ assert [_]is_destructor(d, Ownership);
  //@ assert d == destructor;
  
  d(data);
  //@ close Stack(stack, destructor, Ownership, Tail);
}