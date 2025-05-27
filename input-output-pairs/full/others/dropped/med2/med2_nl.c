#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

/***
 * Description:
 * The create_arraylist function dynamically allocates and initializes a new dynamic array list structure.
 * 
 * @param None
 * 
 * The function allocates memory for a new `struct arraylist` and a block of memory to store up to 100 pointers (`void*`).
 * It sets the size to 0 (indicating the list is currently empty) and the capacity to 100.
 * If either allocation fails, the program aborts.
 * 
 * The returned array list is ready to be used for storing up to 100 elements.
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
 * The clear function deallocates the memory used by an array list and its internal data array.
 * 
 * @param a - a pointer to a previously created array list.
 * 
 * The function frees both the internal data block (array of pointers) and the array list structure itself.
 * After this call, the memory previously used by the array list is fully released.
 */
void clear(struct arraylist* a)
{
  void** data = a->data;
  free(data);
  free(a);
}


/***
 * Description:
 * The main function demonstrates the usage of the array list.
 * 
 * It creates an array list, and then clears it, freeing all memory.
 * The program completes successfully without returning any meaningful result.
 */
int main()
{
  struct arraylist* a = create_arraylist();
  clear(a);

  return 0;
}
