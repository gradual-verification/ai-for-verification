#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& malloc_block_node(from) &*& from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);
@*/

// TODO: make this function pass the verification
struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    //@ close llist(0);
    return 0;
}

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ close llist(new_node);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open llist(head);
        //@ open lseg(head, 0);
        while (curr->next != 0)
        //@ invariant lseg(head, curr) &*& curr != 0 &*& malloc_block_node(curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            struct node *tmp = curr;
            curr = curr->next;
            //@ open lseg(curr, 0);
        }
        curr->next = new_node;
        //@ close lseg(head, 0);
        //@ close llist(head);
        return head;
    }
}

// TODO: make this function pass the verification
void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    //@ open llist(head);
    if (head != 0) {
        //@ open lseg(head, 0);
        dispose_list(head->next);
        free(head);
    } else {
        //@ close lseg(head, 0);
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