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

lemma void lseg_add_node_lemma(struct node* p, struct node* q)
    requires lseg(p, q) &*& q != 0 &*& malloc_block_node(q) &*& q->next |-> ?r;
    ensures lseg(p, r);
{
    open lseg(p, q);
    if (p == q) {
        close lseg(p, r);
    } else {
        lseg_add_node_lemma(p->next, q);
        close lseg(p, r);
    }
}

lemma void lseg_append_lemma(struct node *p, struct node *q)
    requires lseg(p, q) &*& q != 0 &*& malloc_block_node(q) &*& q->next |-> ?r &*& lseg(r, 0);
    ensures lseg(p, 0);
{
    open lseg(p, q);
    if (p == q) {
        close lseg(p, 0);
    } else {
        lseg_append_lemma(p->next, q);
        close lseg(p, 0);
    }
}
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    //@ close lseg(0, 0);
    //@ close llist(0);
    return 0;
}

struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ open llist(head);
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& lseg(curr, 0);
        {
            //@ open lseg(curr, 0);
            struct node *old_curr = curr;
            curr = curr->next;
            //@ lseg_add_node_lemma(head, old_curr);
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ lseg_append_lemma(head, curr);
        //@ close llist(head);
        return head;
    }
}

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    if (head != 0) {
        //@ open llist(head);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open llist(head);
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