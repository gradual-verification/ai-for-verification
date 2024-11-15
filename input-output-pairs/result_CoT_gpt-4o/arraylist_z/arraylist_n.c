#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h> // For INT_MAX and SIZE_MAX
#include "arraylist.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; void** data, int size, int capacity) =
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  data != 0 &*& size >= 0 &*& capacity > 0 &*&
  0 <= size &*& capacity <= INT_MAX &*&
  malloc_block_arraylist(a) &*&
  malloc_block(data, capacity * sizeof(void*));
@*/

/*@
predicate valid_index(struct arraylist* a, int i) =
  arraylist(a, ?data, ?size, ?capacity) &*& 
  0 <= i &*& i < size;
@*/

/*@
predicate valid_list(struct arraylist* a) =
  arraylist(a, ?data, ?size, ?capacity) &*& 
  0 <= size &*& size <= capacity &*& 
  0 < capacity &*& capacity <= INT_MAX;
@*/

/*@
  requires true;
  ensures result != 0 &*& valid_list(result);
@*/
struct arraylist* create_arraylist() 
{
  struct arraylist* a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  return a; 
}

/*@
  requires valid_list(a) &*& valid_index(a, i);
  ensures valid_list(a) &*& result == a->data[i];
@*/
void* list_get(struct arraylist* a, int i)
{
  return a->data[i];
}

/*@
  requires valid_list(a);
  ensures valid_list(a) &*& result == a->size;
@*/
int list_length(struct arraylist* a)
{
  return a->size;
}

/*@
  requires valid_list(a);
  ensures valid_list(a);
@*/
void list_add(struct arraylist* a, void* v) 
{
  int size = a->size;
  void** data = a->data;

  if(a->capacity <= size) {
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    memcpy(newData, data, (size_t)size * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    free(data);
  }
  a->data[size] = v;
  a->size += 1;
}

/*@
  requires valid_list(a) &*& valid_index(a, n);
  ensures valid_list(a);
@*/
void list_remove_nth(struct arraylist* a, int n)
{
  void** data = a->data;
  int size = a->size;
  memmove(data + n, data + n + 1, (size - n - 1) * sizeof(void *));
  a->size = size - 1;
}

/*@
  requires valid_list(a);
  ensures true;
@*/
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  free(data);
  free(a);
}

/*@
  requires true;
  ensures result == 0;
@*/
int main()
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void*)10);
  list_add(a, (void*)20);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*)20);
  list_dispose(a);

  return 0;
}
