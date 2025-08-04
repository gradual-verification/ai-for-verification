#include <stdlib.h>
//@ #include <list.gh>

struct node {
    struct node *next;
};

/*@

predicate lseg(struct node *from, struct node *to, list<struct node *> ps) =
    from == to ?
        ps == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_ps) &*&
        ps == cons(from, tail_ps);

predicate list(struct node *l, list<struct node *> ps) = lseg(l, 0, ps);

lemma void lseg_merge(struct node *n1, struct node *n2)
    requires lseg(n1, n2, ?p1) &*& lseg(n2, 0, ?p2);
    ensures lseg(n1, 0, append(p1, p2));
{
    open lseg(n1, n2, p1);
    if (n1 != n2) {
        lseg_merge(n1->next, n2);
    }
}

lemma void lseg_append_node(struct node *first, struct node *last)
    requires lseg(first, last, ?ps1) &*& last != 0 &*& last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, 0, ?ps2);
    ensures lseg(first, next, append(ps1, cons(last, nil))) &*& lseg(next, 0, ps2);
{
    open lseg(first, last, ps1);
    if (first == last) {
        open lseg(next, 0, ps2);
        close lseg(next, 0, ps2);
    } else {
        lseg_append_node(first->next, last);
    }
    close lseg(first, next, append(ps1, cons(last, nil)));
}

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `append_tail` function appends a new node to the tail of a given list. 
 *
 * @param head: the head to a given list
 * 
 * It makes sure that the returned value is the head of a list. 
 */
struct node *append_tail(struct node *head)
    //@ requires list(head, ?nodes);
    //@ ensures list(result, append(nodes, cons(new_node, nil))) &*& !mem(new_node, nodes) &*& new_node != 0;
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ open list(head, nodes); // nodes == nil
        //@ close lseg(new_node, 0, cons(new_node, nil));
        //@ close list(new_node, cons(new_node, nil));
        return new_node;
    } else {
        struct node *curr = head;
        //@ open list(head, nodes);
        //@ close lseg(head, head, nil);
        while (curr->next != 0)
            /*@
            invariant
                curr != 0 &*&
                lseg(head, curr, ?p) &*&
                lseg(curr, 0, ?s) &*&
                nodes == append(p, s) &*&
                s != nil &*&
                new_node->next |-> 0 &*& malloc_block_node(new_node) &*&
                !mem(new_node, nodes);
            @*/
        {
            struct node *tmp = curr;
            //@ open lseg(curr, 0, s);
            curr = curr->next;
            //@ lseg_append_node(head, tmp);
            //@ append_assoc(p, cons(tmp, nil), tail(s));
        }
        //@ open lseg(curr, 0, s);
        //@ assert s == cons(curr, nil);
        curr->next = new_node;
        //@ close lseg(new_node, 0, cons(new_node, nil));
        //@ close lseg(curr, 0, cons(curr, cons(new_node, nil)));
        //@ lseg_merge(head, curr);
        //@ append_assoc(p, cons(curr, nil), cons(new_node, nil));
        return head;
    }
}