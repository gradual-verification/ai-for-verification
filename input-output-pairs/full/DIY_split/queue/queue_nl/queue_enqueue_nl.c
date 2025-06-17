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
