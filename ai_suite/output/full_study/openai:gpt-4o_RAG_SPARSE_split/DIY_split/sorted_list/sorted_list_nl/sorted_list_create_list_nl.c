#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@
predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->value |-> ?value &*& node->next |-> ?next &*& malloc_block_node(node) &*&
        nodes(next, ?values0) &*& value <= head(values0) &*& values == cons(value, values0);

predicate sorted_list(struct node *node) =
    nodes(node, ?values) &*& sorted(values);

fixpoint bool sorted(list<int> values) {
    switch (values) {
        case nil: return true;
        case cons(h, t): return t == nil || (h <= head(t) && sorted(t));
    }
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_list` function creates an empty list. 
 *
 * The function ensures that the returned value is a sorted list. 
 */
/*@
requires true;
ensures sorted_list(result);
@*/
struct node *create_list()
{
    return 0;
}