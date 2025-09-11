#include "stdlib.h"
  
/*
  Destructors
*/


// TODO: make this function pass the verification
typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, ?info);
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

// Implementation of stack functions to make the verification complete

struct stack* create_stack(destructor* d)
//@ requires [_]is_destructor(d, ?Ownership);
//@ ensures Stack(result, d, Ownership, Nil);
{
    struct stack* s = malloc(sizeof(struct stack));
    if (s == 0) abort();
    s->first = 0;
    s->destructor = d;
    s->size = 0;
    //@ close StackItems(Ownership, 0, Nil);
    //@ close Stack(s, d, Ownership, Nil);
    return s;
}

void stack_push(struct stack* stack, void* data, void* info)
//@ requires Stack(stack, ?d, ?Ownership, ?S) &*& Ownership(data, info);
//@ ensures Stack(stack, d, Ownership, Cons(data, info, S));
{
    //@ open Stack(stack, d, Ownership, S);
    struct node* n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->data = data;
    n->next = stack->first;
    stack->first = n;
    stack->size = stack->size + 1;
    //@ close Node(Ownership, n, data, info, n->next);
    //@ close StackItems(Ownership, n, Cons(data, info, S));
    //@ close Stack(stack, d, Ownership, Cons(data, info, S));
}

void* stack_pop(struct stack* stack)
//@ requires Stack(stack, ?d, ?Ownership, ?S) &*& !IsEmpty(S);
//@ ensures Stack(stack, d, Ownership, Pop(S)) &*& Ownership(result, ?info);
{
    //@ open Stack(stack, d, Ownership, S);
    struct node* first = stack->first;
    //@ open StackItems(Ownership, first, S);
    //@ open Node(Ownership, first, ?data, ?info, ?next);
    void* result = first->data;
    stack->first = first->next;
    stack->size = stack->size - 1;
    free(first);
    //@ close Stack(stack, d, Ownership, Pop(S));
    return result;
}

void stack_dispose(struct stack* stack)
//@ requires Stack(stack, ?d, ?Ownership, ?S);
//@ ensures true;
{
    //@ open Stack(stack, d, Ownership, S);
    struct node* current = stack->first;
    //@ StackItems<void*> items = current;
    while (current != 0)
    //@ invariant StackItems(Ownership, current, ?Remaining);
    {
        //@ open StackItems(Ownership, current, Remaining);
        struct node* next = current->next;
        //@ open Node(Ownership, current, ?data, ?info, next);
        d(current->data);
        free(current);
        current = next;
    }
    //@ open StackItems(Ownership, 0, _);
    free(stack);
}

// Example destructor implementation
void data_destructor(void* data) //@ : destructor<DataCarrier>(Data_Ownership)
//@ requires Data_Ownership(data, ?info);
//@ ensures true;
{
    //@ open Data_Ownership(data, info);
    //@ open Data(data, _, _);
    free(data);
}

int main()
//@ requires true;
//@ ensures true;
{
    //@ close [_]is_destructor<DataCarrier>(data_destructor, Data_Ownership);
    struct stack* s = create_stack(data_destructor);
    
    struct data* d1 = malloc(sizeof(struct data));
    if (d1 == 0) abort();
    d1->foo = 10;
    d1->bar = 20;
    //@ close Data(d1, 10, 20);
    //@ close Data_Ownership(d1, DataCarrier(10, 20));
    
    stack_push(s, d1, DataCarrier(10, 20));
    
    struct data* d2 = malloc(sizeof(struct data));
    if (d2 == 0) abort();
    d2->foo = 30;
    d2->bar = 40;
    //@ close Data(d2, 30, 40);
    //@ close Data_Ownership(d2, DataCarrier(30, 40));
    
    stack_push(s, d2, DataCarrier(30, 40));
    
    stack_dispose(s);
    
    return 0;
}