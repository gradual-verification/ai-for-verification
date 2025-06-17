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
