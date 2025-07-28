#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


// TODO: make this function pass the verification
/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);

