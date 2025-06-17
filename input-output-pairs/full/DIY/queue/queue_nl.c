#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct queue {
    struct node *head;
    struct node *tail;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_queue` function creates an empty heap. 
 *
 * The function makes sure that the returned heap has no element. 
 */
struct queue *create_queue()
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    return q;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `enqueue` function puts a new node with the given value into the tail of a given queue. 
 *
 * @param q: the given queue to be enqueued
 * @param val: the given value to be added
 * 
 * The function makes sure that q has its number of elements incremented by 1. 
 */
void enqueue(struct queue *q, int val)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = val;
    n->next = 0;

    if (q->tail == 0) {
        q->head = n;
        q->tail = n;
    } else {
        q->tail->next = n;
        q->tail = n;
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `dequeue` function removes the head of a non-empty heap and returns its value. 
 *
 * @param q: the given non-empty queue to be dequeued
 * 
 * This function makes sure that q has its number of elements decremented by 1. 
 */
int dequeue(struct queue *q)
{
    struct node *n = q->head;
    int val;

    if (q->head == q->tail) {
        val = q->tail->value;
        q->head = 0;
        q->tail = 0;
        free(n);
    } else {
        val = n->value;
        struct node *next = n->next;
        q->head = next;
        free(n);
    }

    return val;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_queue` function frees an empty queue. 
 *
 * @param q: the given empty queue to be freed
 * 
 * It makes sure that q is freed. 
 */
void dispose_queue(struct queue *q)
{
    free(q);
}
