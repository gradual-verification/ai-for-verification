#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
predicate sorted_list(struct node *n; list<int> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        sorted_list(next, ?tail_values) &*&
        values == cons(v, tail_values) &*&
        (tail_values == nil ? true : v <= head(tail_values));
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_list` function disposes an sorted list. 
 * 
 * @param head: the head of a sorted list
 *
 * The function ensures that the list of head is freed. 
 */
void dispose_list(struct node *head)
    //@ requires sorted_list(head, ?values);
    //@ ensures emp;
{
    if (head != 0) {
        //@ open sorted_list(head, values);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open sorted_list(head, values);
    }
}