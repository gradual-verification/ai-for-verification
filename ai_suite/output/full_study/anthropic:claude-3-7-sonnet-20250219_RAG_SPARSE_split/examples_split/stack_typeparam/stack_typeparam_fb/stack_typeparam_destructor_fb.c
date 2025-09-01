#include "stdlib.h"

/*
  Destructors
*/


// TODO: make this function pass the verification
typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
  //@ ensures true;


/*
  Stack
*/

struct node {
  void* data;
  struct node* next;
};

struct stack {
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

/*
  A few use cases
*/

struct data {
  int foo;
  int bar;
};

/*@

predicate Data(struct data* data, int foo, int bar) =
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

/*@
// Define the is_destructor predicate to verify the destructor function
predicate is_destructor<T>(destructor* d, predicate(void *, T) Ownership) =
    d != 0;

// Define the destructor_function_pointer predicate to link the function pointer to its contract
predicate destructor_function_pointer<T>(destructor* d, predicate(void *, T) Ownership) =
    is_destructor(d, Ownership);
@*/

// Implementation of a destructor for Data
void data_destructor(void* data)
//@ requires Data_Ownership(data, _);
//@ ensures true;
{
    struct data* d = (struct data*)data;
    //@ open Data_Ownership(d, _);
    //@ open Data(d, _, _);
    free(d);
}

// Create a new stack
struct stack* create_stack(destructor* destructor)
//@ requires [_]is_destructor(destructor, ?Ownership);
//@ ensures Stack(result, destructor, Ownership, Nil);
{
    struct stack* stack = malloc(sizeof(struct stack));
    if (stack == 0) abort();
    
    stack->first = 0;
    stack->destructor = destructor;
    stack->size = 0;
    
    //@ close StackItems(Ownership, 0, Nil);
    //@ close Stack(stack, destructor, Ownership, Nil);
    return stack;
}

// Push an item onto the stack
void stack_push(struct stack* stack, void* data)
//@ requires Stack(stack, ?destructor, ?Ownership, ?S) &*& Ownership(data, ?info);
//@ ensures Stack(stack, destructor, Ownership, Cons(data, info, S));
{
    //@ open Stack(stack, destructor, Ownership, S);
    struct node* node = malloc(sizeof(struct node));
    if (node == 0) abort();
    
    node->data = data;
    node->next = stack->first;
    
    stack->first = node;
    stack->size = stack->size + 1;
    
    //@ close Node(Ownership, node, data, info, _);
    //@ close StackItems(Ownership, node, Cons(data, info, S));
    //@ close Stack(stack, destructor, Ownership, Cons(data, info, S));
}

// Pop an item from the stack
void* stack_pop(struct stack* stack)
//@ requires Stack(stack, ?destructor, ?Ownership, ?S) &*& !IsEmpty(S);
//@ ensures Stack(stack, destructor, Ownership, Pop(S)) &*& Ownership(result, ?info);
{
    //@ open Stack(stack, destructor, Ownership, S);
    struct node* node = stack->first;
    //@ open StackItems(Ownership, node, S);
    //@ open Node(Ownership, node, ?data, ?info, ?next);
    
    stack->first = node->next;
    stack->size = stack->size - 1;
    
    void* result = node->data;
    free(node);
    
    //@ close Stack(stack, destructor, Ownership, Pop(S));
    return result;
}

// Check if the stack is empty
bool stack_is_empty(struct stack* stack)
//@ requires Stack(stack, ?destructor, ?Ownership, ?S);
//@ ensures Stack(stack, destructor, Ownership, S) &*& result == IsEmpty(S);
{
    //@ open Stack(stack, destructor, Ownership, S);
    bool result = stack->first == 0;
    //@ close Stack(stack, destructor, Ownership, S);
    return result;
}

// Dispose of the stack and all its items
void stack_dispose(struct stack* stack)
//@ requires Stack(stack, ?destructor, ?Ownership, ?S);
//@ ensures true;
{
    //@ open Stack(stack, destructor, Ownership, S);
    struct node* current = stack->first;
    
    while (current != 0)
    //@ invariant StackItems(Ownership, current, ?S2);
    {
        //@ open StackItems(Ownership, current, S2);
        //@ open Node(Ownership, current, ?data, ?info, ?next);
        
        struct node* next = current->next;
        destructor* d = stack->destructor;
        
        d(current->data);
        free(current);
        
        current = next;
    }
    
    //@ open StackItems(Ownership, 0, _);
    free(stack);
}

// Example usage
int main()
//@ requires true;
//@ ensures true;
{
    //@ close [_]is_destructor(data_destructor, Data_Ownership);
    struct stack* stack = create_stack(data_destructor);
    
    struct data* d1 = malloc(sizeof(struct data));
    if (d1 == 0) abort();
    d1->foo = 10;
    d1->bar = 20;
    //@ close Data(d1, 10, 20);
    //@ close Data_Ownership(d1, DataCarrier(10, 20));
    
    stack_push(stack, d1);
    
    struct data* d2 = malloc(sizeof(struct data));
    if (d2 == 0) abort();
    d2->foo = 30;
    d2->bar = 40;
    //@ close Data(d2, 30, 40);
    //@ close Data_Ownership(d2, DataCarrier(30, 40));
    
    stack_push(stack, d2);
    
    if (!stack_is_empty(stack)) {
        struct data* popped = stack_pop(stack);
        //@ open Data_Ownership(popped, ?dc);
        //@ open Data(popped, _, _);
        free(popped);
    }
    
    stack_dispose(stack);
    
    return 0;
}