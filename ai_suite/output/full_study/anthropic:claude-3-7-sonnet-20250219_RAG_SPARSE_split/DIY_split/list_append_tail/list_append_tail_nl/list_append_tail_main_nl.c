#include <stdlib.h>

/*@
// Define a predicate for a linked list node
predicate node_pred(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& malloc_block_node(n) &*& node_pred(next);
@*/

struct node {
    struct node *next;
};


/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
/*@
// Function specification
requires true;
ensures node_pred(result);
@*/
struct node *create_list()
{
    return 0;
    //@ close node_pred(0);
}

/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
/*@
// Function specification
requires node_pred(head);
ensures node_pred(result);
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close node_pred(0);
    //@ close node_pred(new_node);

    if (head == 0) {
        return new_node;
    } else {
        //@ open node_pred(head);
        struct node *curr = head;
        while (curr->next != 0)
        //@ invariant curr != 0 &*& curr->next |-> ?next &*& node_pred(next);
        {
            struct node *tmp = curr;
            //@ open node_pred(curr->next);
            curr = curr->next;
        }
        curr->next = new_node;
        //@ close node_pred(head);
        return head;
    }
}

/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
/*@
// Function specification
requires node_pred(head);
ensures true;
@*/
void dispose_list(struct node *head)
{
    if (head != 0) {
        //@ open node_pred(head);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open node_pred(head);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of the list. 
 */
/*@
// Function specification
requires true;
ensures true;
@*/
int main()
{
    struct node *list = create_list();
    //@ assert node_pred(list);
    
    list = append_tail(list);
    //@ assert node_pred(list);
    
    list = append_tail(list);
    //@ assert node_pred(list);
    
    list = append_tail(list);
    //@ assert node_pred(list);

    dispose_list(list);
    return 0;
}