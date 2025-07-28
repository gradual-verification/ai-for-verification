#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};


// TODO: make this function pass the verification
/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0. The set is initially empty.
*/
struct set* create_set()
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
  return set;
}

