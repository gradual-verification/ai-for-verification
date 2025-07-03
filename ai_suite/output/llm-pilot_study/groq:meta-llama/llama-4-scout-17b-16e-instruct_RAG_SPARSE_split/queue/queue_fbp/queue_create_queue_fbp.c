#include "stdlib.h"

struct node {
 struct node *next;
 int value;
};

struct queue {
 struct node *head;
 struct node *tail;
};

/*@
predicate lseg(struct node *from, struct node *to; list<int> vs) =
 from == to ?
 vs == nil
 :
 from !=0 &*& from->next |-> ?next &*& from->value |-> ?value &*& lseg(next, to, ?nvs) &*&
 vs == cons(value, nvs) &*& malloc_block_node(from);

predicate queue(struct queue *q, int count) =
 q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
 (count ==0 ?
 tail ==0
 :
 count >0 &*& tail !=0 &*& lseg(head, tail, count -1) &*& tail->value |-> ?v &*& tail->next |->0 &*& malloc_block_node(tail));
@*/

// TODO: make this function pass the verification
struct queue *create_queue()
 //@ requires true;
 //@ ensures queue(result,0);
{
 struct queue *q = malloc(sizeof(struct queue));
 if (q ==0) abort();
 q->head =0;
 q->tail =0;
 //@ close lseg(0, 0, nil);
 //@ close queue(q, 0);
 return q;
}