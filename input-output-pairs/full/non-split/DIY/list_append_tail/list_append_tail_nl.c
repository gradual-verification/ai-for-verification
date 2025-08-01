#include <stdlib.h>

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
struct node *create_list()
{
    return 0;
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        while (curr->next != 0)
        {
            struct node *tmp = curr;
            curr = curr->next;
        }
        curr->next = new_node;
        return head;
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of the list. 
 */
int main()
{
    struct node *list = create_list();
    list = append_tail(list);
    list = append_tail(list);
    list = append_tail(list);

    dispose_list(list);
    return 0;
}