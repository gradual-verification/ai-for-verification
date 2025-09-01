#include "stdlib.h"
#include "assert.h"

/*
  Destructors
*/

typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);
  //@ requires Ownership(data, _);
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
  Ownership(data, info) &*&
  node != 0;

predicate StackItems<T>(predicate(void *, T) Ownership, struct node* head, Stack<T> S) =
  head == 0 ? S == Nil :
  Node(Ownership, head, ?data, ?info, ?next) &*&
  StackItems(Ownership, next, ?T) &*&
  S == Cons(data, info, T);

fixpoint int Size<T>(Stack<T> S)
{
  switch (S)
  {
    case Nil: return 0;
    case Cons(x, y, T): return 1 + Size(T);
  }
}

lemma_auto void Size_Cons<T>(void* data, T info, Stack<T> S)
    requires true;
    ensures Size(Cons(data, info, S)) == 1 + Size(S);
{
}

predicate Stack<T>(struct stack* stack, destructor* destructor, predicate(void *, T) Ownership, Stack<T> S) =
  malloc_block_stack(stack) &*&
  (destructor == 0 ? true : is_destructor<T>(destructor, Ownership)) &*&
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
  switch (Stack)
  {
    case Nil:
      return Nil;

    case Cons(x, y, T):
      return T;
  }
}

lemma_auto void Size_Pop<T>(Stack<T> S)
    requires S != Nil;
    ensures Size(Pop(S)) == Size(S) - 1;
{
    switch(S) { case Nil: case Cons(h, i, t): }
}

fixpoint bool IsEmpty<T>(Stack<T> S)
{
  switch (S)
  {
    case Nil:
      return true;
    
    case Cons(x, y, T):
      return false;
  }
}

@*/

struct stack* create_stack/*@<T>@*/(destructor* d, predicate(void*, T) Ownership)
    //@ requires d == 0 ? true : is_destructor<T>(d, Ownership);
    //@ ensures Stack<T>(result, d, Ownership, Nil);
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

void stack_push/*@<T>@*/(struct stack* s, void* data, T info)
    //@ requires Stack(s, ?d, ?Ownership, ?S) &*& Ownership(data, info);
    //@ ensures Stack(s, d, Ownership, Cons(data, info, S));
{
    //@ open Stack(s, d, Ownership, S);
    //@ open StackItems(Ownership, s->first, S);
    struct node* n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->data = data;
    n->next = s->first;
    //@ close Node(Ownership, n, data, info, s->first);
    //@ close StackItems(Ownership, n, Cons(data, info, S));
    s->first = n;
    s->size = s->size + 1;
    //@ Size_Cons(data, info, S);
    //@ close Stack(s, d, Ownership, Cons(data, info, S));
}

void* stack_pop/*@<T>@*/(struct stack* s)
    //@ requires Stack(s, ?d, ?Ownership, ?S) &*& S != Nil;
    //@ ensures Stack(s, d, Ownership, Pop(S)) &*& Ownership(result, ?info) &*& S == Cons(result, info, Pop(S));
{
    //@ open Stack(s, d, Ownership, S);
    struct node* first = s->first;
    //@ open StackItems(Ownership, first, S);
    //@ open Node(Ownership, first, ?data, ?info, ?next);
    s->first = next;
    s->size = s->size - 1;
    //@ Size_Pop(S);
    free(first);
    //@ close Stack(s, d, Ownership, Pop(S));
    return data;
}

void dispose_stack_nodes/*@<T>@*/(struct node* n, destructor* d, predicate(void*, T) Ownership)
    //@ requires StackItems(Ownership, n, ?S) &*& (d == 0 ? true : is_destructor<T>(d, Ownership));
    //@ ensures true;
{
    if (n == 0) {
        //@ open StackItems(Ownership, n, S);
    } else {
        //@ open StackItems(Ownership, n, S);
        //@ open Node(Ownership, n, ?data, ?info, ?next);
        dispose_stack_nodes(next, d, Ownership);
        if (d != 0) {
            d(data);
        } else {
            //@ leak Ownership(data, info);
        }
        free(n);
    }
}

void stack_dispose/*@<T>@*/(struct stack* s)
    //@ requires Stack(s, ?d, ?Ownership, ?S);
    //@ ensures true;
{
    //@ open Stack(s, d, Ownership, S);
    dispose_stack_nodes(s->first, d, Ownership);
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
  switch (dc)
  {
    case DataCarrier(x, y):
      return x;
  }
}

fixpoint int GetBar(DataCarrier dc)
{
  switch (dc)
  {
    case DataCarrier(x, y):
      return y;
  }
}

predicate Data_Ownership(struct data *data, DataCarrier DC) = Data(data, GetFoo(DC), GetBar(DC));

@*/

void data_destructor(void* p)
    //@ : destructor<DataCarrier, Data_Ownership>
    //@ requires Data_Ownership(p, _);
    //@ ensures true;
{
    //@ open Data_Ownership(p, _);
    struct data* d = (struct data*)p;
    //@ open Data(d, _, _);
    free(d);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    //@ produce_function_pointer_chunk destructor<DataCarrier>(data_destructor)(Data_Ownership);
    struct stack* s = create_stack<DataCarrier>(data_destructor, Data_Ownership);

    struct data* d1 = malloc(sizeof(struct data));
    if (d1 == 0) abort();
    d1->foo = 10; d1->bar = 11;
    //@ close Data(d1, 10, 11);
    //@ close Data_Ownership(d1, DataCarrier(10, 11));
    stack_push(s, d1, DataCarrier(10, 11));

    struct data* d2 = malloc(sizeof(struct data));
    if (d2 == 0) abort();
    d2->foo = 20; d2->bar = 21;
    //@ close Data(d2, 20, 21);
    //@ close Data_Ownership(d2, DataCarrier(20, 21));
    stack_push(s, d2, DataCarrier(20, 21));

    void* p = stack_pop(s);
    struct data* d_pop = (struct data*)p;
    //@ open Data_Ownership(d_pop, ?dc);
    //@ open Data(d_pop, ?foo, ?bar);
    assert(foo == 20);
    assert(bar == 21);
    free(d_pop);

    stack_dispose(s);

    return 0;
}