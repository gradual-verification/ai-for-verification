#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
  
};


/*
  Natural Language Specification:
  - Description: Creates a new, empty set.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to a newly allocated set if successful, or `0` if memory allocation fails. The set is initially empty.
*/
struct set* create_set()
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;

  return set;
}

/*
  Natural Language Specification:
  - Description: Adds a new element to the set.
  - Parameters: 
    - `set`: A pointer to the set.
    - `x`: A pointer to the element to be added.
  - Requires: The set must be valid and `x` must not already be in the set.
  - Ensures: The set is updated to include `x`, and the size of the set is incremented by one.
*/
void set_add(struct set* set, void* x)
{

  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;

}

/*
  Natural Language Specification:
  - Description: Checks whether a given element is present in the set.
  - Parameters: 
    - `set`: A pointer to the set.
    - `x`: A pointer to the element to check for.
  - Requires: The set must be valid.
  - Ensures: Returns `true` if `x` is present in the set, otherwise returns `false`. The set remains unchanged.
*/
bool set_contains(struct set* set, void* x)
{
  struct node* curr = set->head;
  bool found = false;

  while(curr != 0 && ! found) 
  {
  
    if(curr->val == x) {

      found = true;
    }
    curr = curr->next;
  
  }
 
  return found;
}

/*
  Natural Language Specification:
  - Description: Disposes of the set by freeing all allocated memory.
  - Parameters: 
    - `set`: A pointer to the set to be disposed of.
  - Requires: The set must be valid.
  - Ensures: All memory associated with the set is freed, and the set is no longer valid.
*/
void set_dispose(struct set* set)

{
  
  struct node* curr = set->head;
  while(curr != 0) 
    
  {
    
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }
 
  free(set);
}

/*
  Natural Language Specification:
  - Description: Main function demonstrating the use of the set data structure.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Adds elements to the set, checks for their existence, and then disposes of the set.
*/
int main() 
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}
