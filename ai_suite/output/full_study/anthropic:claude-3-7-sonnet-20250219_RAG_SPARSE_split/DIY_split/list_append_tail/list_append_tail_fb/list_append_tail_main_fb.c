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
        //@ close llist(new_node);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open llist(head);
        //@ open lseg(head, 0);
        //@ close lseg(curr, curr);
        while (curr->next != 0)
            /*@ invariant curr != 0 &*& curr->next |-> ?next &*& 
                         lseg(head, curr) &*& lseg(next, 0); @*/
        {
            //@ open lseg(next, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp, curr);
        }
        curr->next = new_node;
        //@ close lseg(new_node, 0);
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
        //@ open lseg(head, 0);
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
    //@ assert llist(list);
    
    list = append_tail(list);
    //@ assert llist(list);
    
    list = append_tail(list);
    //@ assert llist(list);
    
    list = append_tail(list);
    //@ assert llist(list);

    dispose_list(list);
    return 0;
}