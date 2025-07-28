#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);


// TODO: make this function pass the verification
/*cell_equals() function
-params: two cell pointers
-description: compares the values of the two cells.
It ensures that the two cells are unchanged, and the return value is true if the values are equal, false otherwise.
*/
bool cell_equals(struct cell* x1, struct cell* x2) //@: equals
{
  
  return x1->val == x2->val;

}

