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
        //@ open llist(head);
        //@ open lseg(head, 0);
        /*@
        loop_invariant 
            lseg(head, curr) &*& curr != 0 &*&
            curr->next |-> ?next &*& lseg(next, 0);
        @*/
        while (curr->next != 0)
        {
            struct node *tmp = curr;
            //@ open lseg(next, 0);
            curr = curr->next;
            //@ close lseg(tmp, tmp);
            //@ close lseg(tmp, curr);
            //@ append_lseg(head, tmp, curr);
        }
        //@ open lseg(next, 0);
        curr->next = new_node;
        //@ close lseg(new_node, 0);
        //@ close lseg(curr, 0);
        //@ append_lseg(head, curr, 0);
        //@ close llist(head);
        return head;
    }
}

/*@
lemma void append_lseg(struct node *from, struct node *mid, struct node *to)
    requires lseg(from, mid) &*& lseg(mid, to);
    ensures lseg(from, to);
{
    open lseg(from, mid);
    if (from == mid) {
    } else {
        append_lseg(from->next, mid, to);
        close lseg(from, to);
    }
}

lemma void close_llist(struct node *head)
    requires lseg(head, 0);
    ensures llist(head);
{
    close llist(head);
}
@*/

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    if (head != 0) {
        //@ open llist(head);
        //@ open lseg(head, 0);
        dispose_list(head->next);
        free(head);
    } else {
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