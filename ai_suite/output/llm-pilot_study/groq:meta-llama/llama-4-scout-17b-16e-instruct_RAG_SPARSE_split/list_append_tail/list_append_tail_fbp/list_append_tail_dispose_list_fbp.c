#include "stdlib.h"

struct node {
 struct node *next;
};

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

// TODO: make this function pass the verification
void dispose_list(struct node *head)
 //@ requires llist(head);
 //@ ensures true;
{
 if (head !=0) {
 /*@
 invariant lseg(head, ?old_head, ?count);
 decreases count;
 @*/
 dispose_list(head->next);
 free(head);
 } else {
 }
}
#include "stdlib.h"

struct node {
 struct node *next;
};

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

// TODO: make this function pass the verification
void dispose_list(struct node *head)
 //@ requires llist(head);
 //@ ensures true;
{
 if (head !=0) {
 /*@
 invariant lseg(head, ?old_head, ?count);
 decreases count;
 @*/
 dispose_list(head->next);
 free(head);
 } else {
 }
}