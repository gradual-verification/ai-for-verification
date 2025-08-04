#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@

predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?v &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        values == cons(v, rest);

predicate llist(struct llist *list, list<int> values) =
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    (first == 0 ?
        last == 0 &*& values == nil
    :
        lseg(first, last, ?prefix_values) &*&
        last != 0 &*&
        last->value |-> ?last_val &*&
        last->next |-> 0 &*&
        malloc_block_node(last) &*&
        values == append(prefix_values, cons(last_val, nil))
    );

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
        //@ invariant lseg(n, l, _);
    {
        //@ open lseg(n, l, _);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ if (l != 0) open lseg(l, l, _);
    free(l);
    free(list);
}