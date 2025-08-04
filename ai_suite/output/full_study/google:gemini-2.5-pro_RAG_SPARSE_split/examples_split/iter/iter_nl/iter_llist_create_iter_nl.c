#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@

// A linked list segment from `from` to `to`, representing the list of values `vs`.
predicate lseg(struct node *from, struct node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?tail_vs) &*&
        vs == cons(v, tail_vs);

// A box class to logically manage the state of the linked list.
// The state `vs` is the list of integer values.
box_class llist_box(list<int> vs) {
    // The invariant is always true; the box does not own memory chunks itself.
    invariant true;

    // Action to create an iterator. It does not change the list's state.
    // It's used to generate a handle.
    action create_iterator();
        requires true;
        ensures vs == old_vs;

    // A handle representing an active iterator.
    // Its existence prevents actions that would modify the list's state `vs`.
    handle_predicate iterator_handle() {
        // The invariant states that the list's values `vs` must not change.
        // Any action that changes `vs` will not preserve this handle's invariant,
        // and will thus be forbidden by VeriFast if a handle exists.
        invariant vs == old_vs;

        // This handle is preserved by the `create_iterator` action.
        preserved_by create_iterator() {}
    }
}

// Predicate for a linked list. It owns the memory for the list structure
// and its nodes, and it is associated with a box that governs its state.
predicate llist_pred(struct llist *l; box boxId, list<int> vs) =
    l->first |-> ?f &*&
    l->last |-> _ &*& // The `last` pointer is not used in this function, so we ignore its value.
    malloc_block_llist(l) &*&
    lseg(f, 0, vs) &*&
    [_]llist_box(boxId, vs);

// Predicate for an iterator. It owns its own memory and a handle to the
// box of the list it iterates over.
predicate iter_pred(struct iter *it; handle handleId, box boxId) =
    it->current |-> _ &*&
    malloc_block_iter(it) &*&
    [_]llist_box_iterator_handle(handleId, boxId);

@*/


// TODO: make this function pass the verification
/**
 * Description:
The `llist_create_iter` function creates an iterator for a given linked list,
which is located at the first node of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param l - Pointer to the linked list structure.
@return - The created iterator pointing to the first node of linked list.
*/
struct iter *llist_create_iter(struct llist *l)
    //@ requires llist_pred(l, ?boxId, ?vs);
    //@ ensures llist_pred(l, boxId, vs) &*& result != 0 &*& iter_pred(result, ?handleId, boxId);
{
    //@ open llist_pred(l, boxId, vs);
    struct iter *i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    struct node *f = l->first;
    i->current = f;

    /*@
    consuming_box_predicate llist_box(boxId, vs)
    perform_action create_iterator()
    {
        // This block does not need to do anything since the invariant is `true`
        // and the action does not require any specific state.
    }
    producing_box_predicate llist_box(boxId, vs)
    producing_fresh_handle_predicate iterator_handle(?handleId);
    @*/

    //@ close iter_pred(i, handleId, boxId);
    //@ close llist_pred(l, boxId, vs);
    return i;
}