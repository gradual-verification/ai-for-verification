#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct queue {
    struct node *head;
    struct node *tail;
};

/***
 * Description:
 * The `create_queue` function creates an empty heap. 
 *
 * The function allocates memory for a new `queue`, and sets its head and tail as 0.
 * It makes sure that the new queue keeps the queue structure. 
 */
struct queue *create_queue()
{
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    q->head = 0;
    q->tail = 0;
    return q;
}

/***
 * Description:
 * The `enqueue` function puts a new node with the given value into the tail of a given queue. 
 *
 * @param q: the given queue to be enqueued, which keeps the queue structure
 * @param val: the given value to be added
 * 
 * The function allocates memory for a new `node`, sets its value and links it next to the tail of the queue. 
 * It makes sure that the new queue keeps the queue structure and its number of elements is incremented. 
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

/***
 * Description:
 * The `dequeue` function removes the head of a non-empty heap and returns its value. 
 *
 * @param q: the given queue to be dequeued, which keeps the queue structure and is not empty
 * 
 * This function frees the original head and lets the head of new queue be the next node of original head.
 * It makes sure that the new queue keeps the queue structure and its number of elements is decremented. 
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

/***
 * Description:
 * The `dispose_queue` function frees an empty queue. 
 *
 * @param q: the given empty queue to be freed
 * 
 * It makes sure that queue is freed. 
 */
void dispose_queue(struct queue *q)
{
    free(q);
}
