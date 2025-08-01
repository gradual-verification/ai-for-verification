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
