#include <stdlib.h>
#include <limits.h>

// a node of an ascendingly sorted list
struct node {
    int value;
    struct node *next;
};

/*@

// A fixpoint function to check if a list of integers is sorted in ascending order.
fixpoint bool is_sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(h, t): return forall(t, (item)(h <= item)) && is_sorted(t);
    }
}

// A fixpoint function that models the insertion of an element into a sorted list.
fixpoint list<int> insert_sorted(int v, list<int> xs) {
    switch (xs) {
        case nil: return cons(v, nil);
        case cons(h, t): return v <= h ? cons(v, xs) : cons(h, insert_sorted(v, t));
    }
}

// A predicate for the memory layout of a linked list.
predicate list_fp(struct node *l, list<int> vs) =
    l == 0 ?
        vs == nil
    :
        l->value |-> ?v &*&
        l->next |-> ?next &*&
        malloc_block_node(l) &*&
        list_fp(next, ?ts) &*&
        vs == cons(v, ts);

// A predicate for an ascendingly sorted linked list.
predicate sorted_list(struct node *l, list<int> vs) =
    list_fp(l, vs) &*& is_sorted(vs) == true;

// A lemma proving that inserting an element into a sorted list results in a sorted list.
lemma void insert_sorted_preserves_sorted(int v, list<int> xs)
    requires is_sorted(xs) == true;
    ensures is_sorted(insert_sorted(v, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (v <= h) {
            } else {
                insert_sorted_preserves_sorted(v, t);
            }
    }
}

@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `append` function appends a node of given value to a sorted list, and still keeps the list sorted. 
 *
 * @param head: the head of a given sorted list
 * @param val: the given value to be added. It is within the bound of the max and min value of the sorted list. 
 * 
 * It makes sure that the new list is still sorted with the same bound of max and min value. 
 */
struct node *append(struct node *head, int value)
    //@ requires sorted_list(head, ?vs);
    //@ ensures sorted_list(result, insert_sorted(value, vs));
{
    //@ open sorted_list(head, vs);
    //@ open list_fp(head, vs);
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        
        //@ insert_sorted_preserves_sorted(value, vs);
        
        //@ close list_fp(head, vs);
        //@ close list_fp(new_node, cons(value, vs));
        
        //@ assert insert_sorted(value, vs) == cons(value, vs);
        
        //@ close sorted_list(new_node, insert_sorted(value, vs));
        return new_node;
    } else {
        //@ list<int> ts = tail(vs);
        //@ is_sorted(vs);
        //@ close sorted_list(head->next, ts);
        struct node *new_next = append(head->next, value);
        //@ open sorted_list(new_next, insert_sorted(value, ts));
        head->next = new_next;
        
        //@ insert_sorted_preserves_sorted(value, vs);
        
        //@ close list_fp(head, insert_sorted(value, vs));
        //@ close sorted_list(head, insert_sorted(value, vs));
        return head;
    }
}