#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void *> vs) =
    a->data |-> ?data
    &*& a->size |-> ?size
    &*& a->capacity |-> ?capacity
    &*& malloc_block_arraylist(a)
    &*& pointers(data, size, vs)
    &*& pointers_(data + size, capacity - size, _)
    &*& malloc_block_pointers(data, capacity)
    &*& size == length(vs)
    &*& 0 <= size &*& size <= capacity;
@*/


/***
 * Description:
The create_arraylist function allocates memory for a new array list structure.

@param none

The function initializes an array list whose the data points to a newly allocated array and has no element.
*/
struct arraylist *create_arraylist()
    //@ requires true;
    //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  a->size = 0;
  a->capacity = 100;
  void **data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  //@ chars__to_pointers_(data, 100);
  //@ pointers__split(data, 0);
  //@ close pointers(data, 0, nil);
  //@ close arraylist(a, nil);
  return a;
}


/***
 * Description:
The list_get function gets the element of the arraylist whose index is i.
It requires that i is within the range of the arraylist.

@param a - the arraylist to be accessed.
@param i - the index of the element to be returned.

The function ensures that the arraylist is not modified at the end, and the return value is the i-th of the arraylist.
*/
void *list_get(struct arraylist *a, int i)
    //@ requires [?f]arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
    //@ ensures [f]arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open [f]arraylist(a, vs);
  void *result = a->data[i];
  //@ close [f]arraylist(a, vs);
  return result;
}


/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list (struct arraylist).

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.

It makes sure that a new element v is added to the end of the array list.
*/
void list_add(struct arraylist *a, void *v)
    //@ requires arraylist(a, ?vs);
    //@ ensures arraylist(a, append(vs, cons(v, nil)));
{
  //@ open arraylist(a, vs);
  //@ assert a->data |-> ?data_ptr &*& a->size |-> ?size &*& a->capacity |-> ?capacity;
  //@ assert pointers(data_ptr, size, vs);
  //@ assert pointers_(data_ptr + size, capacity - size, _);
  //@ assert malloc_block_pointers(data_ptr, capacity);

  if(a->capacity <= a->size) {
    int old_capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)old_capacity * 2 + 1) abort();
    int new_capacity = old_capacity * 2 + 1;
    if (INT_MAX / 2 - 1 < old_capacity) abort();

    void** newData = malloc((size_t)new_capacity * sizeof(void*));
    if(newData == 0) abort();

    //@ pointers_to_chars(data_ptr);
    //@ assert [1]chars(data_ptr, size * sizeof(void*), ?cs_data);
    memcpy(newData, data_ptr, (size_t)size * sizeof(void*));
    //@ assert chars(newData, size * sizeof(void*), cs_data);

    a->data = newData;
    a->capacity = new_capacity;

    //@ chars_to_chars_(data_ptr);
    //@ pointers__to_chars_(data_ptr + size);
    //@ chars__join(data_ptr);
    free(data_ptr);

    //@ chars_to_pointers(newData, size);
    //@ chars__to_pointers_(newData + size, new_capacity - size);
    //@ assert pointers(newData, size, vs);
    //@ assert pointers_(newData + size, new_capacity - size, _);
    //@ assert malloc_block_pointers(newData, new_capacity);
  }

  //@ assert a->data |-> ?current_data &*& a->size |-> size &*& a->capacity |-> ?current_capacity;
  //@ assert pointers(current_data, size, vs);
  //@ assert pointers_(current_data + size, current_capacity - size, _);
  //@ assert malloc_block_pointers(current_data, current_capacity);

  //@ open pointers_(current_data + size, current_capacity - size, _);
  a->data[size] = v;
  a->size += 1;
  //@ close pointer(current_data + size, v);
  //@ pointers_join(current_data);
  //@ close arraylist(a, append(vs, cons(v, nil)));
}


/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist).

@param a - the arraylist to be de-allocated

This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
    //@ requires arraylist(a, ?vs);
    //@ ensures true;
{
  //@ open arraylist(a, vs);
  //@ pointers_to_pointers_(a->data);
  //@ pointers_pointers__join(a->data);
  //@ pointers__to_chars_(a->data);
  free(a->data);
  free(a);
}


// TODO: make this function pass the verification
/**
 * Description:
The main function tests the operation of an arraylist.
*/
int main()
    //@ requires true;
    //@ ensures true;
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