#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/






/** Description:

 The create_arraylist function allocates memory for a new array list structure. If allocation fails, the program aborts. 
 It initializes the size to 0, then allocates memory for an array of 100 pointers. If this allocation also fails, the program aborts. 
  The function assigns the data pointer to this newly allocated array and sets the capacity to 100. Finally, it returns the initialized array list.


***/




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

//description: get the element of the arraylist which the index is i
void *list_get(struct arraylist *a, int i)
{
  return a->data[i];
}

//description: get the length of the arraylist a
int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, vs) &*& result == length(vs);
{
  return a->size;
}


/**  

description: The list_add function adds a new element to the end of the dynamic array list 
(struct arraylist). If the current size of the array list equals or exceeds its capacity, 
it first doubles the capacity and adds one to it to avoid integer overflow, 
ensuring enough space for new elements. It allocates new memory for the resized array, 
copies existing elements to the new array, and frees the old memory. 
If any memory allocation fails, the program aborts. After ensuring sufficient capacity, 
it adds the new element to the end of the array list and increments the size by one. 
The function uses various assertions and mathematical
 checks to maintain memory safety and prevent overflow conditions.
.
**/

void list_add(struct arraylist *a, void *v)

{
  int size = 0;
  void** data = 0;
  if(a->capacity <= a->size) {
    data = a->data;
    size = a->size;
    int capacity = a->capacity;
    //@ assert capacity == size;
    if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
    //@ mul_mono_l(0, sizeof(void *), capacity * 2 + 1); //how can I know where is the mul_mono_l()? I did not find where they define the mul_mono_l(), It has some lemma? Do I need to write the natural language specification for that?
    //
   
   
    //@ div_rem_nonneg(SIZE_MAX, sizeof(void *));
    //@ mul_mono_l(capacity * 2 + 1, SIZE_MAX / sizeof(void *), sizeof(void *));
    void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
    if(newData == 0) abort();
    //@ pointers__split(newData, size);
    //@ mul_mono_l(0, size, sizeof(void *));
    memcpy(newData, data, (size_t)size * sizeof(void*));
    //@ chars_to_pointers(newData, size);
    a->data = newData;
    //@ div_rem_nonneg(INT_MAX, 2);
    if (INT_MAX / 2 - 1 < capacity) abort();
    a->capacity = capacity * 2 + 1;
    //@ chars_to_pointers(data, size);
    free(data);
  }
  size = a->size;
  data = a->data;
  data[size] = v;
  a->size += 1;
  //@ close pointers(data + size, 1, _);
}

/**
 * 
 * Description:
The list_remove_nth function removes the element at the specified index n from the dynamic array list (struct arraylist). 
It begins by retrieving the current data array and size of the array list. It uses memory safety assertions to handle the pointers properly. 
The function then shifts the elements after the n-th position one place to the left using memmove, effectively removing the n-th element. After the shift, 
it decrements the size of the array list by one. The function ensures that the pointers and memory remain valid and safe throughout the operation.
 * 
 * **/

void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  //@ pointers_limits(data);
  //@ mul_mono_l(0, n, sizeof(void *));
  //@ mul_mono_l(n + 1, length(vs), sizeof(void *));
  //@ pointers_split(data, n);
  //@ open pointers(data + n, _, _);
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  //@ chars_to_pointers(data + n, size - n - 1);
  a->size = a->size - 1;
  //@ chars_to_pointers(data + size - 1, 1);
}
/***
 * Description:
The list_dispose function deallocates the memory associated with a dynamic array list (struct arraylist). 
It first retrieves the data array, size, and capacity of the array list. 
Then, it frees the memory allocated for the data array followed by freeing the memory allocated for the array list structure itself. 
This function ensures that all dynamically allocated memory used by the array list is properly released to prevent memory leaks.
*/
void list_dispose(struct arraylist* a)
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
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
  assert(tmp == (void*) 20);
  list_dispose(a);

  return 0;
}