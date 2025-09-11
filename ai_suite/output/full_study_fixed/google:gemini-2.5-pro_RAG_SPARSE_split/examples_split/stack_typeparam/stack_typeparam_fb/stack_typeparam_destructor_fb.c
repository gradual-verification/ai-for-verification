#include "stdlib.h"

/*
  Destructors
*/


// TODO: make this function pass the verification
typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires this == 0 ? false : Ownership(data, _);
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
  malloc_block_node(node) &*&
  node->data |-> data &*&
  node->next |-> next &*&
  Ownership(data, info);

predicate StackItems<T>(predicate(void *, T) Ownership, struct node* head, Stack<T> S) =
  head == 0 ? S == Nil :
  Node(Ownership, head, ?data, ?info, ?next) &*&
  StackItems(Ownership, next, ?rem_S) &*&
  S == Cons(data, info, rem_S);

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

struct stack* stack_create/*@<T>@*/(destructor* dest, predicate(void*, T) own)
  //@ requires [1]is_destructor(dest, own);
  //@ ensures Stack<T>(result, dest, own, Nil);
{
    struct stack* s = malloc(sizeof(struct stack));
    if (s == 0) abort();
    s->first = 0;
    s->destructor = dest;
    s->size = 0;
    //@ close StackItems<T>(own, 0, Nil);
    //@ leak is_destructor(dest, own);
    //@ close Stack<T>(s, dest, own, Nil);
    return s;
}

void stack_push/*@<T>@*/(struct stack* s, void* data)
  //@ requires Stack<T>(s, ?dest, ?own, ?S) &*& own(data, ?info);
  //@ ensures Stack<T>(s, dest, own, Push(data, info, S));
{
    //@ open Stack<T>(s, dest, own, S);
    struct node* n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->data = data;
    n->next = s->first;
    s->first = n;
    s->size = s->size + 1;
    //@ close Node<T>(own, n, data, info, n->next);
    //@ close StackItems<T>(own, n, Push(data, info, S));
    //@ close Stack<T>(s, dest, own, Push(data, info, S));
}

void* stack_pop/*@<T>@*/(struct stack* s)
  //@ requires Stack<T>(s, ?dest, ?own, ?S) &*& S != Nil;
  //@ ensures Stack<T>(s, dest, own, Pop(S)) &*& own(result, ?info) &*& S == Cons(result, info, Pop(S));
{
    //@ open Stack<T>(s, dest, own, S);
    struct node* first = s->first;
    //@ open StackItems<T>(own, first, S);
    //@ assert Node<T>(own, first, ?data, ?info, ?next);
    //@ open Node<T>(own, first, data, info, next);
    
    void* result = first->data;
    s->first = first->next;
    s->size = s->size - 1;
    free(first);
    
    //@ close Stack<T>(s, dest, own, Pop(S));
    return result;
}

void stack_dispose/*@<T>@*/(struct stack* s)
  //@ requires Stack<T>(s, ?dest, ?own, ?S);
  //@ ensures true;
{
    //@ open Stack<T>(s, dest, own, S);
    struct node* current = s->first;
    destructor* d = s->destructor;
    
    //@ open StackItems<T>(own, current, S);
    while(current != 0)
        //@ invariant current == 0 ? S == Nil : (StackItems<T>(own, current, S) &*& [_]is_destructor(d, own));
    {
        //@ open StackItems<T>(own, current, S);
        //@ assert Node<T>(own, current, ?data, ?info, ?next) &*& StackItems<T>(own, next, ?rem_S) &*& S == Cons(data, info, rem_S);
        //@ open Node<T>(own, current, data, info, next);
        
        struct node* next_node = current->next;
        void* data_ptr = current->data;
        
        if (d != 0) {
            d(data_ptr);
        }
        
        free(current);
        current = next_node;
        //@ S = rem_S;
    }
    
    free(s);
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

void data_destructor(void* data) //@ : destructor<DataCarrier, Data_Ownership>
  //@ requires Data_Ownership(data, _);
  //@ ensures true;
{
  //@ open Data_Ownership(data, _);
  //@ open Data(data, _, _);
  free(data);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack* s = stack_create<DataCarrier>(data_destructor, Data_Ownership);
    
    struct data* d1 = malloc(sizeof(struct data));
    if (d1 == 0) abort();
    d1->foo = 10;
    d1->bar = 20;
    //@ close Data(d1, 10, 20);
    //@ close Data_Ownership(d1, DataCarrier(10, 20));
    stack_push<DataCarrier>(s, d1);
    
    struct data* d2 = malloc(sizeof(struct data));
    if (d2 == 0) abort();
    d2->foo = 30;
    d2->bar = 40;
    //@ close Data(d2, 30, 40);
    //@ close Data_Ownership(d2, DataCarrier(30, 40));
    stack_push<DataCarrier>(s, d2);
    
    struct data* d_pop = stack_pop<DataCarrier>(s);
    //@ open Data_Ownership(d_pop, ?dc);
    //@ assert GetFoo(dc) == 30 && GetBar(dc) == 40;
    //@ open Data(d_pop, 30, 40);
    free(d_pop);
    
    stack_dispose<DataCarrier>(s);
    
    return 0;
}