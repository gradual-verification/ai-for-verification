#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity  &*&
  data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/


// TODO: make this function pass the verification
struct arraylist *create_arraylist() 
  //@ requires true;
  //@ ensures arraylist(result, nil);
{
  struct arraylist *a = malloc(sizeof(struct arraylist));
  if(a == 0) abort();
  
  a->size = 0;
  
  // The type of 'data' is corrected from 'void *' to 'void **' to match the struct field 'a->data'.
  // This is a necessary correction for C type safety and for VeriFast verification.
  void **data = malloc(100 * sizeof(void*));
  if(data == 0) abort();
  
  a->data = data;
  a->capacity = 100;
  
  //@ close arraylist(a, nil);
  
  return a; 
}