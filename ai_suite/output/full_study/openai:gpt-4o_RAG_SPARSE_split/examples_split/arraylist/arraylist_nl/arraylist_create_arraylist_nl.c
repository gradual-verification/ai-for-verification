#include <stdint.h>
#include <stdlib.h>
#include <string.h>

//@ #include "prelude.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@ predicate arraylist(struct arraylist *a, int capacity, list<void *> data) =
//@   a->size |-> length(data) &*& a->capacity |-> capacity &*& a->data |-> ?d &*& pointers(d, capacity, data) &*& malloc_block_pointers(d, capacity) &*& malloc_block_arraylist(a);

struct arraylist *create_arraylist()
  //@ requires true;
  //@ ensures result != 0 ? arraylist(result, 100, nil) : true;
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, 100, nil);
  return a;
}