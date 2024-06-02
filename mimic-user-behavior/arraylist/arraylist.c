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


// Predicate: arraylist

// Description:
// This predicate describes the internal state of a dynamic array represented by a pointer to the struct arraylist 'a'. It associates the array with a list of void pointers 'vs', representing its elements.

// Parameters:
// - a: Pointer to the struct arraylist representing the dynamic array.
// - vs: List of void pointers representing the elements stored in the dynamic array.

// Conditions:
// - 'a' points to a dynamically allocated memory block storing the struct arraylist.
// - 'a' has members:
//   - 'data': Pointer to the actual data storage of the dynamic array.
//   - 'size': Current number of elements in the dynamic array.
//   - 'capacity': Maximum capacity of the dynamic array.
// - Memory blocks allocated for 'a' and its 'data' member are properly managed using malloc_block_arraylist and malloc_block_pointers predicates respectively.
// - The elements of the dynamic array are stored in the memory block pointed to by 'data', from index 0 to 'size', inclusive, and correspond to the elements in the list 'vs'.
// - The remaining space in the 'data' memory block, from index 'size' to 'capacity', is currently unused.

// Overall, this predicate encapsulates the internal representation of a dynamic array and its associated metadata, including size, capacity, and actual data storage, while ensuring proper memory management.



//******///
// Description:
// This function creates a new dynamically allocated array list.

// Preconditions:
// None

// Postconditions:
// - The function returns a pointer to a newly allocated struct arraylist.
// - The returned array list is initialized with no elements.

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

 /**natural language specification: **/
  /**
  Description:
This function creates a new dynamically allocated array list.

Preconditions:
- Assumes an existing array list 'a' with elements 'vs'.
- Requires 'i' to be a valid index within the range of elements in 'vs'.

Postconditions:
- Returns the element at index 'i' in the array list 'vs'.
- The array list 'a' remains unchanged with elements 'vs'.
  
  **/
void *list_get(struct arraylist *a, int i)
  //@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
  //@ ensures arraylist(a, vs) &*& result == nth(i, vs);

 
{
  return a->data[i];
}
//what is the ?vs mark?

int list_length(struct arraylist *a)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, vs) &*& result == length(vs);

/**  
natural language specifications:
Preconditions:
- Assumes an existing array list 'a' with elements 'vs'.

Postconditions:
- Returns the length of the array list 'vs'. and the result should be same as length of the arraylist a
- The array list 'a' remains unchanged with elements 'vs'.**/



{
  return a->size;
}


/**  
natural language specifications:

description: add an element to the list
precondition: arraylist with the each variable name is vs
post condition, the arraylist a and also the arraylist append the v to the original arraylist vs.
**/

void list_add(struct arraylist *a, void *v)
  //@ requires arraylist(a, ?vs);
  //@ ensures arraylist(a, append(vs, cons(v, nil)));





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
This function removes the nth element from the given arraylist. The arraylist is assumed to be non-empty and valid.

Specification:
- Precondition:
  - The arraylist 'a' is a valid arraylist containing elements 'vs'.
  - The value of 'n' is non-negative (0 <= n).
  - The value of 'n' is less than the length of the arraylist ('n < length(vs)').

- Postcondition:
  - The arraylist 'a' after the removal operation contains the elements obtained by appending the sublist 
  that consists of the first 'n' elements of 'vs' with the 
  sublist that consists of the elements from 'vs' starting from the (n+1)th position till the end.
 * 
 * **/

void list_remove_nth(struct arraylist *a, int n)

  //@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
  //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
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
This function disposes of the memory associated with the given arraylist 'a'. It deallocates the memory allocated for the data array and the arraylist structure itself.

Specification:
- Precondition:
  - The arraylist 'a' is a valid arraylist containing elements 'vs'.

- Postcondition:
  - The function has no specific postcondition. It simply deallocates the memory associated with 'a'.
*/
void list_dispose(struct arraylist* a)
  //@ requires arraylist(a, ?vs);
  //@ ensures true;
{
  void** data = a->data;
  int size = a->size;
  int capacity = a->capacity;
  free(data);
  free(a);
}

/***
 * Description:
The main function serves as the entry point for the program. Within this function, an arraylist 'a' is created and populated with elements, and then certain operations are performed on it. Finally, the arraylist 'a' is disposed of, and the program exits.

Specification:

Precondition:
No specific preconditions are required for the main function.
Postcondition:
Upon completion of the function, there are no specific conditions or alterations to the program state. The function simply ensures that the program terminates without errors.
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