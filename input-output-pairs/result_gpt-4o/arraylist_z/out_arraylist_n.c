#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "arraylist.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a, void **data, int size, int capacity) =
  a->data |-> data &*& a->size |-> size &*& a->capacity |-> capacity &*&
  0 <= size &*& size <= capacity &*& malloc_block_arraylist(a) &*& 
  malloc_block_pointer_array(data, capacity);
@*/

/*@
requires true;
ensures result == 0 ? true : arraylist(result, ?data, 0, 100);
*/
struct arraylist *create_arraylist()  
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  a->size = 0;
  void **data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, data, 0, 100);
  return a; 
}

/*@
requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= i &*& i < size;
ensures arraylist(a, data, size, capacity) &*& result == nth(i, ?vs);
*/
void *list_get(struct arraylist *a, int i)
{
  //@ open arraylist(a, ?data, ?size, ?capacity);
  //@ assert data[i] |-> ?v;
  return a->data[i];
  //@ close arraylist(a, data, size, capacity);
}

/*@
requires arraylist(a, ?data, ?size, ?capacity);
ensures arraylist(a, data, size, capacity) &*& result == size;
*/
int list_length(struct arraylist *a)
{
  //@ open arraylist(a, ?data, ?size, ?capacity);
  //@ close arraylist(a, data, size, capacity);
  return a->size;
}

/*@
requires arraylist(a, ?data, ?size, ?capacity);
ensures arraylist(a, ?newData, size + 1, ?newCapacity) &*& newCapacity >= capacity;
*/
void list_add(struct arraylist *a, void *v)
{
  //@ open arraylist(a, ?data, ?size, ?capacity);
  if(a->capacity <= a->size) {
    void** oldData = a->data;
    int oldCapacity = a->capacity;
    size_t newSize = (size_t)oldCapacity * 2 + 1;
    if (SIZE_MAX / sizeof(void *) < newSize) abort();
    void** newData = malloc(newSize * sizeof(void*));
    if(newData == 0) abort();
    memcpy(newData, oldData, (size_t)oldCapacity * sizeof(void*));
    a->data = newData;
    if (INT_MAX / 2 - 1 < oldCapacity) abort();
    a->capacity = oldCapacity * 2 + 1;
    free(oldData);
  }
  a->data[a->size] = v;
  a->size += 1;
  //@ close arraylist(a, a->data, a->size, a->capacity);
}

/*@
requires arraylist(a, ?data, ?size, ?capacity) &*& 0 <= n &*& n < size;
ensures arraylist(a, data, size - 1, capacity);
*/
void list_remove_nth(struct arraylist *a, int n)
{
  //@ open arraylist(a, ?data, ?size, ?capacity);
  memmove(a->data + n, a->data + n + 1, (unsigned int) (a->size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ close arraylist(a, data, a->size, capacity);
}

/*@
requires arraylist(a, ?data, ?size, ?capacity);
ensures true;
*/
void list_dispose(struct arraylist* a)
{
  //@ open arraylist(a, ?data, ?size, ?capacity);
  free(a->data);
  free(a);
}

int main()
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}
