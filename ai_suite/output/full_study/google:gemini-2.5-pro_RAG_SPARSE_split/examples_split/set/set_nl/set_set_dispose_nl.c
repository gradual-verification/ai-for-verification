#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*@
// A predicate representing a well-formed, null-terminated linked list of nodes.
predicate nodes(struct node* n) =
    n == 0 ?
        true
    :
        n->val |-> _ &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        nodes(next);

// A predicate representing a valid set.
predicate set(struct set* s) =
    s->head |-> ?head &*&
    malloc_block_set(s) &*&
    nodes(head);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed. 
*/
void set_dispose(struct set* set)
    //@ requires set(set);
    //@ ensures emp;
{
    //@ open set(set);
    struct node* curr = set->head;
    while(curr != 0)
        //@ invariant nodes(curr) &*& malloc_block_set(set) &*& set->head |-> _;
    {
        //@ open nodes(curr);
        struct node* nxt = curr->next;
        free(curr);
        curr = nxt;
    }
    //@ open nodes(0);
    free(set);
}