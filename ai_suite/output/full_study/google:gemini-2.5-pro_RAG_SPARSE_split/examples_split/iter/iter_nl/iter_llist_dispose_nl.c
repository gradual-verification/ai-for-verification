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
// A list segment from `from` (inclusive) to `to` (exclusive).
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        values == cons(value, rest);

// A linked list with first and last pointers.
predicate llist(struct llist *list, list<int> values) =
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    (
        first == 0 ?
            last == 0 &*& values == nil
        :
            lseg(first, last, ?vals_but_last) &*&
            last != 0 &*&
            last->value |-> ?v_last &*&
            last->next |-> 0 &*&
            malloc_block_node(last) &*&
            values == append(vals_but_last, cons(v_last, nil))
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
    //@ open lseg(n, l, _); // After the loop, n == l. This consumes the lseg(l, l, nil) chunk.

    free(l);
    free(list);
}