#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from->value |-> ?v &*& from->next |-> ?n &*& malloc_block_node(from) &*&
        lseg(n, to, ?vs) &*& values == cons(v, vs);

predicate llist(struct llist *list, list<int> values) =
    list->first |-> ?first &*& list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    lseg(first, last, values) &*& last->next |-> _ &*& last->value |-> _ &*& malloc_block_node(last);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
    //@ requires llist(list, ?values);
    //@ ensures true;
{
    //@ open llist(list, values);
    struct node *n = list->first;
    struct node *l = list->last;
    while (n != l)
        //@ invariant lseg(n, l, ?vs);
    {
        //@ open lseg(n, l, vs);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ open lseg(l, l, _);
    free(l);
    free(list);
}