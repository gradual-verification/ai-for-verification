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
        //@ open lseg(curr, 0);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& curr != 0 &*& malloc_block_node(curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            struct node *tmp = curr;
            curr = curr->next;
            //@ open lseg(curr, 0);
            //@ close lseg(tmp, curr);
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ close lseg(new_node, 0);
        //@ close lseg(curr, 0);
        //@ close lseg(head, 0);
        return head;
    }
}

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    if (head != 0) {
        //@ open lseg(head, 0);
        struct node *next = head->next;
        dispose_list(next);
        free(head);
    } else {
        //@ open lseg(0, 0);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *list = create_list();
    //@ close llist(list);
    list = append_tail(list);
    //@ close llist(list);
    list = append_tail(list);
    //@ close llist(list);
    list = append_tail(list);
    //@ close llist(list);
    dispose_list(list);
    return 0;
}