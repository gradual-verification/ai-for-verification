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
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity  &*&
   &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/



/*@
predicate arraylist_length(struct arraylist *a, int size,int capacity) =
  a->size |->size &*& a->capacity|->capacity;
@*/



//???? 
//? create the connection between data and a->data
//_means all other members, we don't care what the value is




/** Description:

 The create_arraylist function allocates memory for a new array list structure. If allocation fails, the program aborts. 
 It initializes the size to 0, then allocates memory for an array of 100 pointers. If this allocation also fails, the program aborts. 
  The function assigns the data pointer to this newly allocated array and sets the capacity to 100. Finally, it returns the initialized array list.


***/
struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
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
  //@ requires a != NULL &*& i >= 0 &*& i<a->size -1;
 //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
  return a->data[i];
}

//description: get the length of the arraylist a

int list_length(struct arraylist *a)
  //@ requires a != NULL;
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
 //@ requires a != NULL &*& v!=NULL
//@ ensures arraylist(a, append(vs, cons(v, nil)));
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

  //@ requires a != NULL &*& n>=0&*& n<=a->size-1;
 //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
  void** data = a->data;
  int size = a->size;
 
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
 
  a->size = a->size - 1;

}
/***
 * Description:
This function disposes of the memory associated with the given arraylist 'a'. It deallocates the memory allocated for the data array and the arraylist structure itself.


*/
void list_dispose(struct arraylist* a)
  //@ requires a != NULL;
//@ ensures true;
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