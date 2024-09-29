#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

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
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  void *data = 0;
  if(a == 0) abort();
  a->size = 0;
  data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  a->data = data;
  a->capacity = 100;
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
{
  return a->data[i];
}

/***
 * Description:
The list_length function gets the length (i.e., number of elements) of a non-null arraylist. 

@param a - the arraylist whose length is to be retrieved.
*/
int list_length(struct arraylist *a)
{
  return a->size;
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
{
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
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
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
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
{
  void** data = a->data;
  int size = a->size;
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
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
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}

/**
 * Description:
The main function creates an arraylist, adds two elements into it, 
gets the first one and asserts on its value, and finally dispose the arraylist.
*/
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