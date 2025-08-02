#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate nodes(struct node *n) =
    n == 0 ? true : n->next |-> ?next &*& malloc_block(n, sizeof(struct node)) &*& nodes(next);
@*/

/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
struct node *create_list()
    //@ requires true;
    //@ ensures nodes(result);
{
    //@ close nodes(0);
    return 0;
}

/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
struct node *append_tail(struct node *head)
    //@ requires nodes(head);
    //@ ensures nodes(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ close nodes(new_node);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open nodes(curr);
        while (curr->next != 0)
            //@ invariant nodes(curr);
        {
            //@ open nodes(curr);
            curr = curr->next;
        }
        curr->next = new_node;
        //@ close nodes(head);
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
void dispose_list(struct node *head)
    //@ requires nodes(head);
    //@ ensures true;
{
    if (head != 0) {
        //@ open nodes(head);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open nodes(head);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of the list. 
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *list = create_list();
    list = append_tail(list);
    list = append_tail(list);
    list = append_tail(list);

    dispose_list(list);
    return 0;
}