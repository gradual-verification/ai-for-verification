#include <stdlib.h>

/*@
predicate lseg(struct node *from, struct node *to) =
  from == to ?
  true
  :
  from !=0 &*& malloc_block_node(from) &*& from->next |-> ?next &*&
  lseg(next, to);

predicate llist(struct node *head) =
  lseg(head,0);
@*/

struct node {
  struct node *next;
};

/*@
lemma void lseg_nil(struct node *to)
requires lseg(0, to);
ensures true;

lemma void lseg_cons(struct node *from, struct node *to)
requires lseg(from, ?next) &*& from != 0 &*& from->next |-> to &*& malloc_block_node(from);
ensures lseg(from, to);
@*/

// TODO: make this function pass the verification
struct node *create_list()
  //@ requires true;
  //@ ensures llist(result);
{
  return 0;
}