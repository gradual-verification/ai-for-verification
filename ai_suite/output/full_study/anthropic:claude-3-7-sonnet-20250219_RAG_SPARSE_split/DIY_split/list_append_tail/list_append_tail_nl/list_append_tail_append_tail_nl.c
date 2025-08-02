#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// Define a predicate for a linked list
predicate node_list(struct node *head; list<struct node *> nodes) =
    head == 0 ?
        nodes == nil
    :
        head->next |-> ?next &*& malloc_block_node(head) &*&
        node_list(next, ?tail) &*& nodes == cons(head, tail);
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
/*@
// Function contract
requires node_list(head, ?nodes);
ensures node_list(result, ?new_nodes) &*& 
        head == 0 ? 
            length(new_nodes) == 1 &*& result != 0
        : 
            length(new_nodes) == length(nodes) + 1 &*& result == head;
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ close node_list(new_node, cons(new_node, nil));
        return new_node;
    } else {
        struct node *curr = head;
        //@ open node_list(head, nodes);
        //@ assert curr->next |-> ?next;
        //@ assert node_list(next, ?tail);
        //@ close node_list(head, nodes);
        
        while (curr->next != 0)
        /*@
        invariant node_list(head, nodes) &*& 
                  mem(curr, nodes) == true &*& 
                  curr != 0 &*& curr->next |-> ?curr_next &*& 
                  malloc_block_node(curr) &*& 
                  new_node != 0 &*& new_node->next |-> 0 &*& 
                  malloc_block_node(new_node);
        @*/
        {
            //@ open node_list(head, nodes);
            //@ assert head->next |-> ?head_next;
            //@ assert node_list(head_next, ?head_tail);
            
            struct node *tmp = curr;
            //@ assert tmp->next |-> ?tmp_next;
            curr = curr->next;
            
            //@ assert mem(curr, nodes);
            //@ close node_list(head, nodes);
        }
        
        //@ open node_list(head, nodes);
        //@ assert curr->next |-> 0;
        curr->next = new_node;
        
        /*@
        // Helper lemma to append a node to the end of a list
        {
            // Define a recursive lemma to help with the verification
            lemma void append_to_list(struct node *h, list<struct node *> ns)
                requires h != 0 &*& h->next |-> ?n &*& malloc_block_node(h) &*& 
                         node_list(n, ?t) &*& ns == cons(h, t) &*&
                         new_node != 0 &*& new_node->next |-> 0 &*& malloc_block_node(new_node);
                ensures node_list(h, append(ns, cons(new_node, nil)));
            {
                open node_list(n, t);
                if (n == 0) {
                    // Base case: we're at the end of the list
                    h->next = new_node;
                    close node_list(new_node, cons(new_node, nil));
                    close node_list(h, cons(h, cons(new_node, nil)));
                } else {
                    // Recursive case: continue down the list
                    append_to_list(n, t);
                    close node_list(h, append(ns, cons(new_node, nil)));
                }
            }
            
            if (head != 0) {
                append_to_list(head, nodes);
            }
        }
        @*/
        
        //@ close node_list(head, append(nodes, cons(new_node, nil)));
        return head;
    }
}
#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// Define a predicate for a linked list
predicate node_list(struct node *head; list<struct node *> nodes) =
    head == 0 ?
        nodes == nil
    :
        head->next |-> ?next &*& malloc_block_node(head) &*&
        node_list(next, ?tail) &*& nodes == cons(head, tail);

// Helper lemma to append a node to the end of a list
lemma void append_node_to_list(struct node *head, struct node *new_node)
    requires node_list(head, ?nodes) &*& head != 0 &*& 
             new_node != 0 &*& new_node->next |-> 0 &*& malloc_block_node(new_node);
    ensures node_list(head, append(nodes, cons(new_node, nil)));
{
    open node_list(head, nodes);
    if (head->next == 0) {
        // Base case: head is the last node
        head->next = new_node;
        close node_list(new_node, cons(new_node, nil));
        close node_list(head, append(nodes, cons(new_node, nil)));
    } else {
        // Recursive case: continue with the next node
        append_node_to_list(head->next, new_node);
        close node_list(head, append(nodes, cons(new_node, nil)));
    }
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
/*@
// Function contract
requires node_list(head, ?nodes);
ensures node_list(result, ?new_nodes) &*& 
        head == 0 ? 
            length(new_nodes) == 1 &*& result != 0
        : 
            length(new_nodes) == length(nodes) + 1 &*& result == head;
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ close node_list(new_node, cons(new_node, nil));
        return new_node;
    } else {
        struct node *curr = head;
        while (curr->next != 0)
        {
            struct node *tmp = curr;
            curr = curr->next;
        }
        curr->next = new_node;
        
        //@ append_node_to_list(head, new_node);
        return head;
    }
}
#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// Define a predicate for a linked list
predicate node(struct node *n, struct node *next) =
    n->next |-> next &*& malloc_block_node(n);

predicate lseg(struct node *from, struct node *to; list<struct node *> nodes) =
    from == to ?
        nodes == nil
    :
        node(from, ?next) &*& lseg(next, to, ?tail) &*& nodes == cons(from, tail);
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
/*@
// Function contract
requires lseg(head, 0, ?nodes);
ensures lseg(result, 0, ?new_nodes) &*& 
        head == 0 ? 
            length(new_nodes) == 1 &*& result != 0
        : 
            length(new_nodes) == length(nodes) + 1 &*& result == head;
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close node(new_node, 0);
    //@ close lseg(new_node, 0, cons(new_node, nil));

    if (head == 0) {
        return new_node;
    } else {
        //@ open lseg(head, 0, nodes);
        //@ assert node(head, ?next);
        
        struct node *curr = head;
        
        /*@
        // Helper lemma to find the last node in a list
        lemma void find_last_node(struct node *start, struct node *end)
            requires lseg(start, end, ?ns) &*& start != end &*& lseg(new_node, 0, ?new_ns);
            ensures lseg(start, new_node, ?prefix) &*& lseg(new_node, 0, new_ns) &*& 
                    append(prefix, new_ns) == append(ns, new_ns);
        {
            open lseg(start, end, ns);
            assert node(start, ?next);
            if (next == end) {
                // Found the last node
                start->next = new_node;
                close lseg(start, new_node, cons(start, nil));
            } else {
                // Continue searching
                find_last_node(next, end);
                close lseg(start, new_node, cons(start, ?rest));
            }
        }
        @*/
        
        while (curr->next != 0)
        {
            struct node *tmp = curr;
            curr = curr->next;
        }
        curr->next = new_node;
        
        //@ find_last_node(head, 0);
        return head;
    }
}
#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// Define a predicate for a linked list
predicate nodes(struct node *n; list<struct node *> ns) =
    n == 0 ?
        ns == nil
    :
        n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?tail) &*& ns == cons(n, tail);
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
/*@
// Function contract
requires nodes(head, ?ns);
ensures result != 0 &*& nodes(result, ?new_ns) &*& 
        head == 0 ? 
            new_ns == cons(result, nil)
        : 
            result == head &*& length(new_ns) == length(ns) + 1;
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        //@ close nodes(new_node, cons(new_node, nil));
        return new_node;
    } else {
        struct node *curr = head;
        //@ open nodes(head, ns);
        //@ assert curr->next |-> ?next;
        //@ assert nodes(next, ?tail);
        //@ close nodes(head, ns);
        
        while (curr->next != 0)
        /*@
        invariant curr != 0 &*& curr->next |-> ?curr_next &*& malloc_block_node(curr) &*&
                  nodes(head, ns) &*& mem(curr, ns) == true;
        @*/
        {
            struct node *tmp = curr;
            curr = curr->next;
        }
        
        curr->next = new_node;
        
        /*@
        // Helper lemma to append a node to the end of a list
        lemma void append_to_list(struct node *h, list<struct node *> ns)
            requires nodes(h, ns) &*& h != 0 &*& mem(?last, ns) == true &*& 
                     last->next |-> new_node &*& last->next |-> 0 &*& 
                     new_node != 0 &*& new_node->next |-> 0 &*& malloc_block_node(new_node);
            ensures nodes(h, ?new_ns) &*& length(new_ns) == length(ns) + 1;
        {
            open nodes(h, ns);
            if (h == last) {
                close nodes(new_node, cons(new_node, nil));
                close nodes(h, cons(h, cons(new_node, nil)));
            } else {
                append_to_list(h->next, tail);
                close nodes(h, cons(h, ?new_tail));
            }
        }
        @*/
        
        //@ append_to_list(head, ns);
        return head;
    }
}
#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
// Define a predicate for a linked list
predicate nodes(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next);
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
/*@
// Function contract
requires nodes(head);
ensures nodes(result);
@*/
struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close nodes(0);
    //@ close nodes(new_node);

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        //@ open nodes(head);
        //@ assert curr->next |-> ?next;
        //@ assert nodes(next);
        //@ close nodes(head);
        
        while (curr->next != 0)
        /*@
        invariant curr != 0 &*& curr->next |-> ?curr_next &*& 
                  malloc_block_node(curr) &*& nodes(curr_next) &*& nodes(new_node);
        @*/
        {
            struct node *tmp =