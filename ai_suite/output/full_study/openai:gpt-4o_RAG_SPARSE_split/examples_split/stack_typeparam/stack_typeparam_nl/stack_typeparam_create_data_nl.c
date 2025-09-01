#include "stdlib.h"

struct node {
  void* data;
  struct node* next;
};

struct stack {
  struct node* first;
  destructor* destructor;
  int size;
};

struct data {
  int foo;
  int bar;
};

//@ predicate data(struct data* d; int foo, int bar) = d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);

struct data* create_data(int foo, int bar)
  //@ requires true;
  //@ ensures result != 0 ? data(result, foo, bar) : true;
{
  struct data* data = malloc(sizeof(struct data));
  if (data == 0) abort();
  
  data->foo = foo;
  data->bar = bar;
  //@ close data(data, foo, bar);
  return data;
}