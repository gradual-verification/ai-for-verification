#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate malloc_block_arraylist(struct arraylist *a) = malloc_block(a, sizeof(struct arraylist));

predicate arraylist(struct arraylist *a; list<void *> vs) =
    a->data |-> ?data
    &*& a->size |-> ?size
    &*& a->capacity |-> ?capacity
    &*& malloc_block_arraylist(a)
    &*& size == length(vs)
    &*& 0 <= size &*& size <= capacity
    &*& data == 0 ?
        capacity == 0
    :
        pointers(data, size, vs) &*&
        pointers_(data + size, capacity - size, _) &*&
        malloc_block_pointers(data, capacity);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list (struct arraylist).

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.

It makes sure that a new element v is added to the end of the array list. 
*/
void list_add(struct arraylist *a, void *v)
/*@
requires arraylist(a, ?vs) &*& pointer_within_limits(v) == true;
ensures arraylist(a, append(vs, cons(v, nil)));
@*/
{
  //@ open arraylist(a, vs);
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    //@ assert a->size |-> ?size_val &*& a->capacity |-> ?cap_val &*& size_val == cap_val;
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    int new_capacity = capacity * 2 + 1;
    void** newData = malloc(((size_t)new_capacity) * sizeof(void*));
    if(newData == 0) abort();
    //@ malloc_block_pointers(newData, new_capacity);
    //@ assert has_type(newData, &typeid(void*)) == true;
    //@ chars__to_pointers_(newData, new_capacity);

    //@ pointers_to_chars(data);
    //@ pointers__split(newData, size);
    //@ pointers__to_chars_(newData);
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ chars_to_pointers(newData, size);

    a->data = newData;
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = new_capacity;
    
    //@ chars_to_chars_(data);
    free(data);
  }
  
  //@ assert a->data |-> ?current_data &*& a->size |-> ?current_size &*& a->capacity |-> ?current_capacity;
  //@ assert current_data == 0 ? current_capacity == 0 : pointers(current_data, current_size, vs) &*& pointers_(current_data + current_size, current_capacity - current_size, _) &*& malloc_block_pointers(current_data, current_capacity);
  
  size = a->size;
  data = a->data;
  
  //@ open pointers_(data + size, _, _);
  data[size] = v;
  //@ close pointer(data + size, v);
  //@ close pointers(data + size, 1, cons(v, nil));
  
  a->size += 1;
  
  //@ pointers_join(data);
  //@ close arraylist(a, append(vs, cons(v, nil)));
}