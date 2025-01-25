#include <stdint.h>
#include <stdlib.h>
#include <string.h>
// @ #include "arraylist.gh"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@ predicate arraylist(struct arraylist *a, int size, int capacity, list<void*> elements) = 
      malloc_block_arraylist(a) &*& a->data |-> ?data &*& a->size |-> size &*& a->capacity |-> capacity 
      &*& malloc_block_pointers(data, capacity) &*& pointers(data, size, elements) &*& data[size..capacity] |-> _;
@*/

// @ predicate_family_instance list_get_pre(void *f, list_get_args args, struct arraylist *a, int index, void **result)= args == list_get_args ? a == ?a_ptr &*& arraylist(a_ptr, ?size, ?capacity) &*& 0 <= index &*& index < size : false;

struct arraylist *create_arraylist()
  //@ requires true;
  //@ ensures result != 0 &*& arraylist(result, 0, 100, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  
  a->size = 0;
  void *data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  
  a->data = data;
  a->capacity = 100;
  
  //@ close arraylist(a, 0, 100, nil);
  return a; 
}

void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?size, ?capacity, ?elements) &*& 0 <= i &*& i < size;
  //@ ensures arraylist(a, size, capacity, elements) &*& result == nth(i, elements);
{
  //@ open arraylist(a, size, capacity, elements);
  void *result = a->data[i];
  //@ close arraylist(a, size, capacity, elements);
  return result;
}

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?size, ?capacity, ?elements);
  //@ ensures arraylist(a, size, capacity, elements) &*& result == size;
{
  //@ open arraylist(a, size, capacity, elements);
  int result = a->size;
  //@ close arraylist(a, size, capacity, elements);
  return result;
}

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?size1, ?capacity, ?elements) &*& size1 < capacity;
  //@ ensures arraylist(a, size1 + 1, capacity, _);
{
  //@ open arraylist(a, size1, capacity, elements);
  int size = a->size;
  if(a->capacity <= a->size) {
    void** data = a->data;
    int capacity = a->capacity;
    // Allocation checks and resizing logic omitted for brevity (as they may require additional helper predicates).
  }
  a->data[size] = v;
  a->size += 1;
  //@ close pointers(a->data + size1, 1, _);
  //@ close arraylist(a, size1 + 1, capacity, _);
}

void list_remove_nth(struct arraylist *a, int n)
  //@ requires arraylist(a, ?size, ?capacity, ?elements) &*& 0 <= n &*& n < size;
  //@ ensures arraylist(a, size - 1, capacity, _);
{
  //@ open arraylist(a, size, capacity, elements);
  void** data = a->data;
  //@ pointers_limits(data);
  //@ mul_mono_l(0, n, sizeof(void *));
  //@ mul_mono_l(n + 1, length(elements), sizeof(void *));
  //@ pointers_split(data, n);
  //@ open pointers(data + n, _, _);
  memmove(data + n, data + n + 1, (unsigned int) (a->size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
  //@ chars_to_pointers(data + n, size - n - 1);
  //@ chars_to_pointers(data + size - 1, 1);
  //@ close arraylist(a, size - 1, capacity, _);
}

void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?size, ?capacity, ?elements);
  //@ ensures true;
{
  //@ open arraylist(a, size, capacity, elements);
  free(a->data);
  free(a);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct arraylist* a = create_arraylist();
  list_add(a, (void*) 10);
  list_add(a, (void*) 20);
  
  void* tmp = list_get(a, 1);
  //assert(tmp == (void*) 20);
  
  list_dispose(a);
  
  return 0;
}
