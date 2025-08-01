#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
}

struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
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

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

// TODO: make this function pass the verification
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