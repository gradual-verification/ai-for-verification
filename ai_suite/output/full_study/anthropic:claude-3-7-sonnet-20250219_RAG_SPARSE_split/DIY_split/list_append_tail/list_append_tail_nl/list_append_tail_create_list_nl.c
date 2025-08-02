#include <stdlib.h>

/*@
predicate lseg(struct node *from, struct node *to; list<void *> values) =
    from == to ?
        values == nil
    :
        from != 0 &*& from->next |-> ?next &*& malloc_block_node(from) &*&
        lseg(next, to, ?tail) &*& values == cons(0, tail);

predicate list(struct node *head; list<void *> values) =
    lseg(head, 0, values);
@*/

struct node {
    struct node *next;
};

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
/*@
// Specification for create_list
requires true;
ensures list(result, nil);
@*/
struct node *create_list()
{
    return 0;
    //@ close list(0, nil);
}