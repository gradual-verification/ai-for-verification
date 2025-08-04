#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// A predicate for the memory block of a single node.
predicate malloc_block_node(struct node* n) = malloc_block(n, sizeof(struct node));

// A linked list segment from 'from' to 'to'.
// This version owns the memory of the nodes in the segment.
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& from->next |-> ?next &*& malloc_block_node(from) &*&
        lseg(next, to);

// A null-terminated linked list.
predicate llist(struct node *head) =
    lseg(head, 0);

// Lemma to "attach" a node at the end of a list segment.
lemma void lseg_append_node(struct node *first, struct node *last)
    requires lseg(first, last) &*& last != 0 &*& last->next |-> ?next &*& malloc_block_node(last);
    ensures lseg(first, next);
{
    open lseg(first, last);
    if (first != last) {
        lseg_append_node(first->next, last);
    }
    close lseg(first, next);
}

// Lemma for transitivity of list segments.
lemma void lseg_trans(struct node *p1, struct node *p2, struct node *p3)
    requires lseg(p1, p2) &*& lseg(p2, p3);
    ensures lseg(p1, p3);
{
    open lseg(p1, p2);
    if (p1 != p2) {
        lseg_trans(p1->next, p2, p3);
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
    //@ malloc_block_node(new_node);
    new_node->next = 0;
    //@ close lseg(new_node, 0);
    //@ close llist(new_node);

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        //@ open llist(head);
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& llist(curr) &*& curr != 0;
        {
            //@ open llist(curr);
            //@ open lseg(curr, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ lseg_append_node(head, tmp);
            //@ close llist(curr);
        }
        //@ open llist(curr);
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ lseg_append_node(head, curr);
        //@ open llist(new_node);
        //@ lseg_trans(head, new_node, 0);
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
        dispose_list(head->next);
        free(head);
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