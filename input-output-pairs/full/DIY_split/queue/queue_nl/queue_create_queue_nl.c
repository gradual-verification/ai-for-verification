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
