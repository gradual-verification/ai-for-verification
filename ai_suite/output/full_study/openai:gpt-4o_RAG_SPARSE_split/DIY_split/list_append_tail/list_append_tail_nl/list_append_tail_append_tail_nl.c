#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate nodes(struct node *n; list<struct node *> nodes) =
    n == 0 ? 
        nodes == nil 
    : 
        n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?nextNodes) &*& nodes == cons(n, nextNodes);

predicate list(struct node *head; list<struct node *> nodes) =
    nodes(head, nodes);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
/*@
requires list(head, ?nodes);
ensures list(result, append(nodes, cons(?newNode, nil))) &*& result == head || result == newNode;
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ close nodes(new_node, cons(new_node, nil));
        //@ close list(new_node, cons(new_node, nil));
        return new_node;
    } else {
        struct node *curr = head;
        //@ open nodes(curr, _);
        while (curr->next != 0)
        //@ invariant nodes(curr, ?currNodes) &*& mem(curr, currNodes) == true;
        {
            //@ open nodes(curr, _);
            curr = curr->next;
        }
        //@ open nodes(curr, _);
        curr->next = new_node;
        //@ close nodes(new_node, cons(new_node, nil));
        //@ close nodes(curr, append(take(index_of(curr, currNodes), currNodes), cons(curr, cons(new_node, nil))));
        //@ close list(head, append(currNodes, cons(new_node, nil)));
        return head;
    }
}