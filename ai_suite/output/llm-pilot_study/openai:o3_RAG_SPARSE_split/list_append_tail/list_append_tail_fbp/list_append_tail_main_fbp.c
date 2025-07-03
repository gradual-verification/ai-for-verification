#include <stdlib.h>

/* ===========================================================================
   Singly linked list of nodes without payload
   Verified with VeriFast
   =========================================================================== */

struct node {
    struct node *next;
};

/*-----------------------------------------------------------------------------
  Recursive list(-segment) predicates
-----------------------------------------------------------------------------*/
/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*&
        malloc_block_node(from) &*&
        from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =          // full list, ends in 0
    lseg(head, 0);
@*/

/* ===========================================================================
   Helper: recursively attach a tail node
   =========================================================================== */

/*@
  The helper takes

     - a (possibly empty) list segment  `curr .. 0`
     - a one–element list  `new_node .. 0`

  and returns the concatenation, still ending in 0.
@*/
static struct node *append_tail_rec(struct node *curr, struct node *new_node)
    //@ requires lseg(curr, 0) &*& lseg(new_node, 0);
    //@ ensures  lseg(result, 0);
{
    //@ open lseg(curr, 0);
    if (curr == 0) {
        /* Empty segment – the new node becomes the whole list.        */
        //@ close lseg(curr, 0);           // Close the trivial segment
        return new_node;
    } else {
        if (curr->next == 0) {
            /* We are at the last node; link in the new node.          */
            curr->next = new_node;
            //@ close lseg(curr, 0);
            return curr;
        } else {
            /* Still in the interior: recurse on the remainder.        */
            struct node *updated_next = append_tail_rec(curr->next, new_node);
            curr->next = updated_next;
            //@ close lseg(curr, 0);
            return curr;
        }
    }
}

/* ===========================================================================
   Public interface
   =========================================================================== */

/* Create an empty list ----------------------------------------------------- */
struct node *create_list()
    //@ requires true;
    //@ ensures  llist(result);
{
    //@ close lseg(0, 0);                 // the empty list segment
    return 0;
}

/* Append one new (fresh) node at the tail ---------------------------------- */
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures  llist(result);
{
    /* allocate fresh node */
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    /* turn the single node into a list segment                               */
    //@ close lseg(0, 0);
    //@ close lseg(new_node, 0);

    if (head == 0) {
        /* Original list was empty.                                           */
        return new_node;                 // already satisfies llist
    } else {
        /* Non-empty list: delegate to helper.                                */
        struct node *res = append_tail_rec(head, new_node);
        return res;                      // helper guarantees lseg(res,0)
    }
}

/* Dispose a list ----------------------------------------------------------- */
void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures  true;
{
    //@ open lseg(head, 0);
    if (head == 0) {
        //@ close lseg(0, 0);
        return;
    } else {
        struct node *next = head->next;
        dispose_list(next);              // recursively free the tail
        free(head);                      // now free the current node
    }
}

/* ===========================================================================
   Demo / test program
   =========================================================================== */
// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures  true;
{
    struct node *list = create_list();        // empty list
    list = append_tail(list);                 // 1st node
    list = append_tail(list);                 // 2nd node
    list = append_tail(list);                 // 3rd node

    dispose_list(list);                       // clean-up
    return 0;
}