#include <stdlib.h>
#include <limits.h>

struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *n, int lower_bound, int upper_bound) =
    n == 0 ?
        lower_bound <= upper_bound
    :
        malloc_block_node(n) &*&
        n->value |-> ?v &*& lower_bound <= v &*& v <= upper_bound &*&
        n->next |-> ?next &*& sorted_list(next, v, upper_bound);
@*/

/*@
///////////////////////////////////////////////////////////////////////////////
// Auxiliary lemma: lowering the lower-bound keeps the list sorted
///////////////////////////////////////////////////////////////////////////////
lemma void sorted_list_weaken_lower(struct node *n,
                                    int old_lower, int new_lower,
                                    int upper)
    requires sorted_list(n, old_lower, upper) &*& new_lower <= old_lower;
    ensures  sorted_list(n, new_lower, upper);
{
    open sorted_list(n, old_lower, upper);
    if (n == 0) {
        // We only need to re-close the empty case.
        close sorted_list(n, new_lower, upper);
    } else {
        // The contents of the node have remained unchanged.
        close sorted_list(n, new_lower, upper);
    }
}
@*/

//----------------------------------------------------------------------------
// Inserting ‘value’ while keeping the list sorted
//----------------------------------------------------------------------------
struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?lower, ?upper) &*& lower <= value &*& value <= upper;
    //@ ensures  sorted_list(result, lower, upper);
{
    //-------------------- empty list ----------------------------------------
    if (head == 0) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next  = 0;
        //@ close malloc_block_node(new_node);
        //@ close sorted_list(0, value, upper);
        //@ close sorted_list(new_node, lower, upper);
        return new_node;
    }

    //-------------------- non-empty list ------------------------------------
    //@ open sorted_list(head, lower, upper);
    int  head_val = head->value;
    struct node *next = head->next;

    //-------------------- insert in front -----------------------------------
    if (value <= head_val) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next  = head;
        //@ close malloc_block_node(new_node);

        // Values in the old list are ≥ head_val and therefore ≥ value
        //@ sorted_list_weaken_lower(head, head_val, value, upper);

        //@ close sorted_list(new_node, lower, upper);
        return new_node;
    }
    //-------------------- insert further in the list ------------------------
    else {
        struct node *new_next = append(next, value);
        head->next = new_next;
        //@ close sorted_list(head, lower, upper);
        return head;
    }
}