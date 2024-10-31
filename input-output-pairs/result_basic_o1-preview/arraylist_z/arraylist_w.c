#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/*@
predicate pointers(void** arr, int n; list<void*> vs) =
    n == 0 ? emp &*& vs == nil :
    arr[0] |-> ?v &*& pointers(arr + 1, n - 1, ?vs0) &*& vs == cons(v, vs0);

lemma void pointers_nth(void **arr, int n, list<void *> vs, int i)
    requires pointers(arr, n, vs) &*& 0 <= i &*& i < n;
    ensures pointers(arr, n, vs) &*& arr[i] |-> nth(i, vs);
{
    open pointers(arr, n, vs);
    if (i == 0) {
    } else {
        pointers_nth(arr + 1, n - 1, tail(vs), i - 1);
    }
    close pointers(arr, n, vs);
}

lemma void pointers_copy(void **src, int n, list<void*> vs, void **dest)
    requires pointers(src, n, vs) &*& malloc_block(dest, n * sizeof(void*)) &*& chars((void*)dest, n * sizeof(void*), _);
    ensures pointers(src, n, vs) &*& pointers(dest, n, vs);
{
    if(n == 0) {
        close pointers(dest, 0, nil);
    } else {
        open pointers(src, n, vs);
        void *v = head(vs);
        pointers_copy(src + 1, n - 1, tail(vs), dest + 1);
        dest[0] = v;
        close pointers(dest, n, vs);
        close pointers(src, n, vs);
    }
}

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
    a->data |-> ?data &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    0 <= size &*& size <= capacity &*&
    malloc_block(a, sizeof(struct arraylist)) &*&
    malloc_block(data, capacity * sizeof(void *)) &*&
    pointers(data, size, vs) &*&
    chars((void*)(data + size), (capacity - size) * sizeof(void *), _);
@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  //@ malloc_block(a, sizeof(struct arraylist));
  void **data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  //@ malloc_block(data, 100 * sizeof(void *));
  a->size = 0;
  a->capacity = 100;
  a->data = data;
  //@ pointers(data, 0, nil);
  //@ chars((void*)(data + 0), (100 - 0) * sizeof(void *), _);
  //@ close arraylist(a, nil);
  return a; 
}

void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?vs) &*& i >= 0 &*& i < length(vs);
  //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void **data = a->data;
  int size = a->size;
  //@ open pointers(data, size, vs);
  //@ pointers_nth(data, size, vs, i);
  void *result = data[i];
  //@ close pointers(data, size, vs);
  //@ close arraylist(a, vs);
  return result;
}

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, vs) &*& result == length(vs);
{
  //@ open arraylist(a, vs);
  int size = a->size;
  //@ close arraylist(a, vs);
  return size;
}

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  //@ open arraylist(a, vs);
  void **data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  if(capacity <= size) {
    int newCapacity = capacity * 2 + 1;
    if (SIZE_MAX / sizeof(void *) < (size_t)newCapacity) abort();
    void **newData = malloc(newCapacity * sizeof(void*));
    if(newData == 0) abort();
    //@ malloc_block(newData, newCapacity * sizeof(void *));
    //@ pointers_copy(data, size, vs, newData);
    //@ chars((void*)(newData + size), (newCapacity - size) * sizeof(void *), _);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    a->data = newData;
    a->capacity = newCapacity;
    //@ a->data |-> newData;
    //@ a->capacity |-> newCapacity;
    //@ open pointers(data, size, vs);
    //@ open chars((void*)(data + size), (capacity - size) * sizeof(void *), _);
    //@ malloc_block(data, capacity * sizeof(void *));
    free(data);
    //@ free_block(data);
    data = newData;
    capacity = newCapacity;
  }
  //@ open chars((void*)(data + size), (capacity - size) * sizeof(void *), _);
  //@ chars((void*)(data + size + 1), (capacity - size -1 ) * sizeof(void *), _);
  data[size] = v;
  //@ data[size] |-> v;
  size = size +1;
  a->size = size;
  //@ a->size |-> size;
  //@ pointers(data, size, append(vs, cons(v, nil)));
  //@ chars((void*)(data + size), (capacity - size) * sizeof(void *), _);
  //@ close arraylist(a, append(vs, cons(v, nil)));
}

void list_remove_nth(struct arraylist *a, int n)
  //@ requires arraylist(a, ?vs) &*& n >= 0 &*& n < length(vs);
  //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  //@ open pointers(data, size, vs);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  //@ open pointers(data + n + 1, size - n -1, drop(n+1, vs));
  //@ pointers(data + n, size - n -1, drop(n+1, vs));
  //@ data[n] |-> nth(n+1, vs);
  //@ close pointers(data + n, size - n -1, drop(n+1, vs));
  //@ pointers(data, size -1, append(take(n, vs), drop(n+1, vs)));
  size = size -1;
  a->size = size;
  //@ a->size |-> size;
  //@ chars((void*)(data + size), (a->capacity - size) * sizeof(void *), _);
  //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}

void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?vs);
  //@ ensures true;
{
  //@ open arraylist(a, vs);
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  //@ open pointers(data, size, vs);
  //@ open chars((void*)(data + size), (capacity - size) * sizeof(void *), _);
  //@ malloc_block(data, capacity * sizeof(void *));
  free(data);
  //@ free_block(data);
  //@ malloc_block(a, sizeof(struct arraylist));
  free(a);
  //@ free_block(a);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);

  tmp = list_get(a, 1);
  //@ assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}
