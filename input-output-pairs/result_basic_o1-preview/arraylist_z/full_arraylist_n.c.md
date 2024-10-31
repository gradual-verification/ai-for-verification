```c
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
//@ #include <limits.h>

/*@
#define VOIDPTR_MAX ((void *)(UINTPTR_MAX))

predicate pointer_array(void **arr, int n, list<void*> vs) =
  n == 0 ? emp :
  arr[0..n] |-> vs;

lemma void array_split(void **arr, int m, int n)
    requires pointer_array(arr, m + n, ?vs);
    ensures pointer_array(arr, m, take(m, vs)) &*& pointer_array(arr + m, n, drop(m, vs));
{
    open pointer_array(arr, m + n, vs);
    split_pointer_array(arr, m);
    close pointer_array(arr, m, take(m, vs));
    close pointer_array(arr + m, n, drop(m, vs));
}

lemma void array_join(void **arr, int m, int n)
    requires pointer_array(arr, m, ?vs1) &*& pointer_array(arr + m, n, ?vs2);
    ensures pointer_array(arr, m + n, append(vs1, vs2));
{
    open pointer_array(arr, m, vs1);
    open pointer_array(arr + m, n, vs2);
    combine_pointer_arrays(arr, m);
    close pointer_array(arr, m + n, append(vs1, vs2));
}

predicate arraylist(struct arraylist *a; list<void *> vs) =
    malloc_block_arraylist(a) &*&
    a->size |-> ?size &*&
    a->capacity |-> ?capacity &*&
    a->data |-> ?data &*&
    0 <= size &*& size <= capacity &*&
    malloc_block(data, capacity * sizeof(void *)) &*&
    pointer_array(data, capacity, ?elems) &*&
    vs == take(size, elems);

@*/

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/***
 * Description:
The create_arraylist function allocates memory for a new array list structure. If allocation fails, the program aborts. 
It initializes the size to 0, then allocates memory for an array of 100 pointers. If this allocation also fails, the program aborts. 
The function assigns the data pointer to this newly allocated array and sets the capacity to 100. Finally, it returns the initialized array list.

@param none
*/
struct arraylist *create_arraylist()
    //@ requires true;
    //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void **data = 0;
  if(a == 0) abort();
  //@ malloc_block_arraylist(a);
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  //@ malloc_block(data, 100 * sizeof(void *));
  //@ close pointer_array(data, 100, repeat(VOIDPTR_MAX, 100));
  a->data = data;
  a->capacity = 100;
  //@ close arraylist(a, nil);
  return a; 
}

/***
 * Description:
The list_get function gets the element of the arraylist whose index is i. 
It requires that i is within the range of the arraylist.

@param a - the arraylist to be accessed.
@param i - the index of the element to be returned.

The function ensures that the arraylist is not modified at the end.
*/
void *list_get(struct arraylist *a, int i)
    //@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
    //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  //@ open arraylist(a, vs);
  void *result = a->data[i];
  //@ close arraylist(a, vs);
  return result;
}

/***
 * Description:
The list_add function adds a new element to the end of the dynamic array list 
(struct arraylist). If the current size of the array list equals or exceeds its capacity, 
it first doubles the capacity and adds one to it to avoid buffer overflow, 
ensuring enough space for new elements. It allocates new memory for the resized array, 
copies existing elements to the new array, and frees the old memory. 
If any memory allocation fails, the program aborts. After ensuring sufficient capacity, 
it adds the new element to the end of the array list and increments the size by one. 
The function uses various assertions and mathematical
checks to maintain memory safety and prevent overflow conditions.

@param a - the arraylist to be added to.
@param v - the new element to be added into the arraylist.
*/
void list_add(struct arraylist *a, void *v)
    //@ requires arraylist(a, ?vs);
    //@ ensures arraylist(a, append(vs, {v}));
{
  //@ open arraylist(a, vs);
  int size = a->size;
  if(a->capacity <= size) {
    int capacity = a->capacity;
    // Ensure no integer overflow
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    void **newData = malloc(((size_t)capacity * 2 +1) * sizeof(void *));
    if(newData == 0) abort();
    //@ malloc_block(newData, ((size_t)capacity * 2 +1) * sizeof(void *));
    //@ array_split(a->data, size, capacity - size);
    //@ chars_to_pointer_array(a->data + size, capacity - size);
    memcpy(newData, a->data, size * sizeof(void *));
    //@ pointer_array(newData, size, vs);
    //@ close pointer_array(newData + size, capacity + capacity +1 - size, repeat(VOIDPTR_MAX, capacity + capacity +1 - size));
    //@ pointer_array_to_chars(a->data + size, capacity - size);
    free(a->data);
    //@ free_block(a->data);
    a->data = newData;
    a->capacity = capacity *2 +1;
  }
  a->data[size] = v;
  a->size = size +1;
  //@ array_split(a->data, size, a->capacity - size);
  //@ open pointer_array(a->data, size, vs);
  //@ close pointer_array(a->data, size +1, append(vs, {v}));
  //@ close pointer_array(a->data + size +1, a->capacity - (size +1), drop(size +1, repeat(VOIDPTR_MAX, a->capacity)));
  //@ array_join(a->data, size +1, a->capacity - (size +1));
  //@ close arraylist(a, append(vs, {v}));
}

/***
 * Description:
The list_remove_nth function removes the element at the specified index n from the dynamic array list (struct arraylist). 
It begins by retrieving the current data array and size of the array list. It uses memory safety assertions to handle the pointers properly. 
The function then shifts the elements after the n-th position one place to the left using memmove, effectively removing the n-th element. After the shift, 
it decrements the size of the array list by one. The function ensures that the pointers and memory remain valid and safe throughout the operation.

@param a - the non-empty arraylist whose element will be removed.
@param n - the index of the element to be removed in the original arraylist, should be within the range of arraylist.
*/
void list_remove_nth(struct arraylist *a, int n)
    //@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
    //@ ensures arraylist(a, remove_nth(n, vs));
{
  //@ open arraylist(a, vs);
  int size = a->size;
  memmove(a->data + n, a->data + n + 1, (unsigned int)(size - n -1)* sizeof(void *));
  a->size = size -1;
  //@ array_split(a->data, size, a->capacity - size);
  //@ open pointer_array(a->data, size, vs);
  //@ list<void*> vs1 = take(n, vs);
  //@ list<void*> vs2 = drop(n +1, vs);
  //@ close pointer_array(a->data, size -1, append(vs1, vs2));
  //@ close pointer_array(a->data + size -1, a->capacity - (size -1), drop(size, repeat(VOIDPTR_MAX, a->capacity)));
  //@ array_join(a->data, size -1, a->capacity - (size -1));
  //@ close arraylist(a, append(vs1, vs2));
}

/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist). 
It first retrieves the data array, size, and capacity of the array list. 
Then, it frees the memory allocated for the data array followed by freeing the memory allocated for the array list structure itself. 
This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.

@param a - the arraylist to be de-allocated.
*/
void list_dispose(struct arraylist* a)
    //@ requires arraylist(a, ?vs);
    //@ ensures true;
{
  //@ open arraylist(a, vs);
  free(a->data);
  //@ free_block(a->data);
  free(a);
  //@ free_block_arraylist(a);
}

/***
 * Description:
The main function creates an arraylist, adds two elements into it, 
gets the first one and asserts on its value, and finally dispose the arraylist.
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
```
