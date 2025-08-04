#include "stdlib.h"
//@ #include "list.gh"

struct node {
  void* value;
  struct node* next;
};

/*@
// A predicate to represent a linked list abstractly.
// 'n' is the head pointer of the C list.
// 'vs' is the abstract list of 'void*' values.
predicate list(struct node *n, list<void*> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next, ?rest) &*&
        vs == cons(v, rest);
@*/


// TODO: make this function pass the verification
/*add() function
-params: struct node* n, void* v
-description: add a new element to the list. 
It requires that n is the starting node of the list. 
It ensures that the element is added to the head of the list.
*/
struct node* add(struct node* n, void* v)
    //@ requires list(n, ?vs);
    //@ ensures list(result, cons(v, vs));
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}