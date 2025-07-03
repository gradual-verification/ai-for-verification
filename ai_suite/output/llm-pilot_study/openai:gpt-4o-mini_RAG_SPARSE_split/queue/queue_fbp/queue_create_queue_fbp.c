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
predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*& from->value |-> ?v &*& from->next |-> ?next &*& malloc_block_node(from) &*& lseg(next, to, ?nvs) &*&
        vs == cons(v, nvs);

predicate queue(struct queue *q, list<int> vs) =
    q->head |-> ?head &*& q->tail |-> ?tail &*& malloc_block_queue(q) &*&
    (tail == 0 ? head == 0 &*& vs == nil : head != 0 &*& lseg(head, tail, vs) &*& tail->next |-> 0 &*& tail->value |-> ?v);
@*/

// TODO: make this function pass the verification
struct queue *create_queue()
    //@ requires exists<predicate(list<int> xs)>(?I) &*& I(nil);
    //@ ensures result == 0 ? I(nil) : queue(result, I);
{
    //@ open exists(I);
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    //@ close queue(q, nil);
    return q;
}

// TODO: make this function pass the verification
void enqueue(struct queue *q, int x)
    //@ requires queue(q, ?vs);
    //@ ensures queue(q, append(vs, {x}));
{
    //@ open queue(q, vs);
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->value = x;
    new_node->next = 0;

    if (q->tail == 0) {
        // Queue is empty
        q->head = new_node;
        q->tail = new_node;
    } else {
        // Queue is not empty
        q->tail->next = new_node;
        q->tail = new_node;
    }
    //@ close queue(q, append(vs, {x}));
}

// TODO: make this function pass the verification
bool try_dequeue(struct queue *q, int *res)
    //@ requires queue(q, ?vs) &*& res |-> _ &*& vs != nil;
    //@ ensures queue(q, ?vs0) &*& vs0 == tail(vs) &*& result ? *res |-> head(vs) : true;
{
    //@ open queue(q, vs);
    if (q->head == 0) {
        // Queue is empty
        //@ close queue(q, vs);
        return false;
    } else {
        struct node *old_head = q->head;
        *res = old_head->value;
        q->head = old_head->next;
        if (q->head == 0) {
            // Queue is now empty
            q->tail = 0;
        }
        free(old_head);
        //@ close queue(q, tail(vs));
        return true;
    }
}

// TODO: make this function pass the verification
void queue_dispose(struct queue *q)
    //@ requires queue(q, _);
    //@ ensures true;
{
    //@ open queue(q, _);
    struct node *current = q->head;
    while (current != 0) 
        //@ invariant lseg(current, 0, _);
    {
        struct node *next = current->next;
        free(current);
        current = next;
    }
    free(q);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct queue *q = create_queue();
    enqueue(q, 10);
    enqueue(q, 20);
    int res;
    if (try_dequeue(q, &res)) {
        // Successfully dequeued
    }
    queue_dispose(q);
    return 0;
}