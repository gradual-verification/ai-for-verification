#include "stdlib.h"

/*
  Destructors
*/

// TODO: make this function pass the verification
/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
//@ requires exists<destructor>(?d) &*& d == this;
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

predicate nodes(struct node* n, list<void*> values, destructor* d) =
  n == 0 ?
    values == nil
  :
    n->data |-> ?data &*& n->next |-> ?next &*& malloc_block_node(n) &*&
    nodes(next, ?values0, d) &*& values == cons(data, values0) &*&
    is_destructor(d) == true &*& d(data);

predicate stack(struct stack* s, list<void*> values, destructor* d) =
  s->first |-> ?first &*& s->destructor |-> d &*& s->size |-> length(values) &*&
  malloc_block_stack(s) &*& nodes(first, values, d);

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
predicate data(struct data* d, int foo, int bar) =
  d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);
@*/

void data_destructor(void* data) //@ : destructor
  //@ requires data(data, ?foo, ?bar);
  //@ ensures true;
{
  struct data* d = data;
  //@ open data(d, foo, bar);
  free(d);
}

struct stack* create_stack(destructor* d)
  //@ requires is_destructor(d) == true;
  //@ ensures stack(result, nil, d);
{
  struct stack* s = malloc(sizeof(struct stack));
  if (s == 0) { abort(); }
  s->first = 0;
  s->destructor = d;
  s->size = 0;
  //@ close nodes(0, nil, d);
  //@ close stack(s, nil, d);
  return s;
}

void stack_push(struct stack* s, void* data)
  //@ requires stack(s, ?values, ?d) &*& is_destructor(d) == true &*& d(data);
  //@ ensures stack(s, cons(data, values), d);
{
  //@ open stack(s, values, d);
  struct node* n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->data = data;
  n->next = s->first;
  s->first = n;
  s->size++;
  //@ close nodes(n, cons(data, values), d);
  //@ close stack(s, cons(data, values), d);
}

void* stack_pop(struct stack* s)
  //@ requires stack(s, ?values, ?d) &*& values != nil;
  //@ ensures stack(s, tail(values), d) &*& result == head(values) &*& d(result);
{
  //@ open stack(s, values, d);
  struct node* n = s->first;
  //@ open nodes(n, values, d);
  void* data = n->data;
  s->first = n->next;
  s->size--;
  free(n);
  //@ close stack(s, tail(values), d);
  return data;
}

void stack_dispose(struct stack* s)
  //@ requires stack(s, ?values, ?d);
  //@ ensures true;
{
  //@ open stack(s, values, d);
  struct node* n = s->first;
  while (n != 0)
    //@ invariant nodes(n, ?vs, d);
  {
    //@ open nodes(n, vs, d);
    struct node* next = n->next;
    void* data = n->data;
    d(data);
    free(n);
    n = next;
  }
  //@ open nodes(0, _, d);
  free(s);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct stack* s = create_stack(data_destructor);
  struct data* d1 = malloc(sizeof(struct data));
  if (d1 == 0) { abort(); }
  d1->foo = 1;
  d1->bar = 2;
  //@ close data(d1, 1, 2);
  stack_push(s, d1);

  struct data* d2 = malloc(sizeof(struct data));
  if (d2 == 0) { abort(); }
  d2->foo = 3;
  d2->bar = 4;
  //@ close data(d2, 3, 4);
  stack_push(s, d2);

  struct data* popped = stack_pop(s);
  //@ open data(popped, 3, 4);
  free(popped);

  stack_dispose(s);
  return 0;
}