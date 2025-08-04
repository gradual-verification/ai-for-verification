#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// A list segment from 'from' to 'to'.
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to);

// A null-terminated list is a segment from 'head' to 0.
predicate list(struct node *head) = lseg(head, 0);

// Lemma to prove that two adjacent list segments can be combined.
lemma void lseg_append(struct node *p)
    requires lseg(p, ?q) &*& lseg(q, ?r);
    ensures lseg(p, r);
{
    open lseg(p, q);
    if (p != q) {
        lseg_append(p->next);
    }
}
@*/

/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
struct node *create_list()
    //@ requires true;
    //@ ensures list(result);
{
    //@ close lseg(0, 0);
    return 0;
}

/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
struct node *append_tail(struct node *head)
    //@ requires list(head);
    //@ ensures list(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close list(new_node);

    if (head == 0) {
        return new_node;
    } else {
        //@ open list(head);
        struct node *curr = head;
        while (curr->next != 0)
            /*@
            invariant curr != 0 &*& lseg(head, curr) &*&
                      curr->next |-> ?next &*& malloc_block_node(curr) &*&
                      list(next);
            @*/
        {
            struct node *old_curr = curr;
            curr = curr->next;
            //@ open list(curr);
            //@ close lseg(old_curr, curr);
            //@ lseg_append(head);
        }
        
        //@ open list(curr->next); // curr->next is 0, so list(0) is true.
        curr->next = new_node;
        
        //@ close lseg(curr, new_node);
        //@ lseg_append(curr);
        //@ lseg_append(head);
        return head;
    }
}

/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
void dispose_list(struct node *head)
    //@ requires list(head);
    //@ ensures true;
{
    //@ open list(head);
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function tests the operations of the list. 
 */
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