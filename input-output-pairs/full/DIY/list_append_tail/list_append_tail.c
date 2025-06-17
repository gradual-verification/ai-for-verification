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

lemma void lseg_merge(struct node *x, struct node *y, struct node *z)
    requires lseg(x, y) &*& lseg(y, z) &*& lseg(z, 0);
    ensures lseg(x, z) &*& lseg(z, 0);
{
    open lseg(x, y);
    if (x == y) {
    } else {
        lseg_merge(x->next, y, z);
        open lseg(z, 0);
        close lseg(x, z);
        close lseg(z, 0);
    }
}
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
    //@ close lseg(0, 0);
    //@ close llist(0);
}

struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    //@ open llist(head);
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node->next, 0);
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ open lseg(head, 0);
        //@ close llist(new_node);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open lseg(head, 0);
        //@ close lseg(head, curr);
        while (curr->next != 0)
        //@ invariant curr != 0 &*& lseg(head, curr) &*& malloc_block_node(curr) &*& curr->next |-> ?cn &*& lseg(cn, 0);
        {
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(cn, cn);
            //@ close lseg(tmp, cn);
            //@ lseg_merge(head, tmp, cn);
            //@ open lseg(cn, 0);
        }
        curr->next = new_node;
        //@ close lseg(curr, 0);
        //@ lseg_merge(head, curr, 0);
        //@ open lseg(0, 0);
        //@ close llist(head);
        return head;
    }
}

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    //@ open llist(head);
    if (head != 0) {
        //@ open lseg(head, 0);
        //@ close llist(head->next);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open lseg(head, 0);
    }
}

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