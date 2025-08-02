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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0);
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    //@ open queue(q, count);
    if (q->tail == 0) {
        //@ assert count == 0;
        q->head = n;
        q->tail = n;
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->tail != 0;
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ assert q->tail->value |-> ?tail_val;
        //@ assert q->tail->next |-> 0;
        
        q->tail->next = n;
        q->tail = n;
        
        //@ close lseg(q->head, q->tail, count);
        //@ close queue(q, count + 1);
    }
}
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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        head == 0 &*& tail == 0
    :
        count > 0 &*& head != 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0) &*&
    malloc_block_queue(q);
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;
    
    //@ open queue(q, count);
    if (q->tail == 0) {
        //@ assert count == 0;
        //@ assert q->head == 0;
        q->head = n;
        q->tail = n;
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->head != 0;
        //@ assert q->tail != 0;
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ assert q->tail->value |-> ?tail_val;
        //@ assert q->tail->next |-> 0;
        
        q->tail->next = n;
        q->tail = n;
        
        //@ close lseg(q->head, n, count);
        //@ close queue(q, count + 1);
    }
}
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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        head == 0 &*& tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0) &*&
    malloc_block_queue(q);
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;
    
    //@ open queue(q, count);
    if (q->tail == 0) {
        //@ assert count == 0;
        //@ assert q->head == 0;
        q->head = n;
        q->tail = n;
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->tail != 0;
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ assert q->tail->value |-> ?tail_val;
        //@ assert q->tail->next |-> 0;
        
        q->tail->next = n;
        q->tail = n;
        
        //@ close lseg(q->head, n, count);
        //@ close queue(q, count + 1);
    }
}
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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        head == 0 &*& tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0) &*&
    malloc_block_queue(q);
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;
    //@ malloc_block_node(n);
    
    //@ open queue(q, count);
    if (q->tail == 0) {
        //@ assert count == 0;
        //@ assert q->head == 0;
        q->head = n;
        q->tail = n;
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->tail != 0;
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ assert q->tail->value |-> ?tail_val;
        //@ assert q->tail->next |-> 0;
        
        q->tail->next = n;
        q->tail = n;
        
        //@ close lseg(q->head, n, count);
        //@ close queue(q, count + 1);
    }
}
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
predicate lseg(struct node *from, struct node *to, int count) =
    from == to ?
        count == 0
    :
        count > 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*& lseg(next, to, count - 1);

predicate queue(struct queue *q, int count) =
    q->head |-> ?head &*& q->tail |-> ?tail &*&
    (count == 0 ?
        head == 0 &*& tail == 0
    :
        count > 0 &*& tail != 0 &*& lseg(head, tail, count - 1) &*& tail->value |-> ?v &*& tail->next |-> 0 &*& malloc_block_node(tail)) &*&
    malloc_block_queue(q);
@*/

void enqueue(struct queue *q, int val)
    //@ requires queue(q, ?count);
    //@ ensures queue(q, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;
    
    //@ open queue(q, count);
    if (q->tail == 0) {
        //@ assert count == 0;
        //@ assert q->head == 0;
        q->head = n;
        q->tail = n;
        //@ close queue(q, count + 1);
    } else {
        //@ assert count > 0;
        //@ assert q->tail != 0;
        //@ assert lseg(q->head, q->tail, count - 1);
        //@ assert q->tail->value |-> ?tail_val;
        //@ assert q->tail->next |-> 0;
        //@ assert malloc_block_node(q->tail);
        
        q->tail->next = n;
        q->tail = n;
        
        //@ close lseg(q->head, n, count);
        //@ close queue(q, count + 1);
    }
}