#include <stdlib.h>

struct node {
    struct node *next;
};

/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the new empty list has the list property. 
 */
struct node *create_list()
{
    return 0;
}

/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list, which has the list property
 * It makes sure that the new list (being returned) keeps the list property. 
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

/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list, which has the list property
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