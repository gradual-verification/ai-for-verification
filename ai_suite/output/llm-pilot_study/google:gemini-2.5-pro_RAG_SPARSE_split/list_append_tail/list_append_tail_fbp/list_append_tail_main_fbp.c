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

lemma void lseg_add_node(struct node *from, struct node *to, struct node *next_node)
    requires lseg(from, to) &*& to != 0 &*& malloc_block_node(to) &*& to->next |-> next_node;
    ensures lseg(from, next_node);
{
    open lseg(from, to);
    if (from == to) {
        close lseg(next_node, next_node);
        close lseg(from, next_node);
    } else {
        lseg_add_node(from->next, to, next_node);
        close lseg(from, next_node);
    }
}
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

    open llist(head);
    if (head == 0) {
        //@ open lseg(0, 0);
        //@ close lseg(0, 0);
        //@ close lseg(new_node, 0);
        //@ close llist(new_node);
        return new_node;
    } else {
        struct node *curr = head;
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& lseg(curr, 0) &*& head != 0;
        {
            //@ open lseg(curr, 0);
            struct node *old_curr = curr;
            curr = curr->next;
            lseg_add_node(head, old_curr, curr);
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        lseg_add_node(head, curr, new_node);
        lseg_add_node(head, new_node, 0);
        //@ close llist(head);
        return head;
    }
}

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    open llist(head);
    open lseg(head, 0);
    if (head != 0) {
        struct node *next = head->next;
        close llist(next);
        dispose_list(next);
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