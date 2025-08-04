#include <stdlib.h>

// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@

// Predicate for a single list node
predicate list_node(struct list_node *n; int v, struct list_node *next) =
    n->value |-> v &*&
    n->next |-> next &*&
    malloc_block_list_node(n);

// Predicate for a list segment from 'from' to 'to'
predicate lseg(struct list_node *from, struct list_node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        list_node(from, ?v, ?next) &*&
        lseg(next, to, ?tail) &*&
        vs == cons(v, tail);

// Predicate for a list segment starting from a pointer-to-pointer
predicate lseg_p(struct list_node **from, struct list_node *to; list<int> vs) =
    pointer(from, ?h) &*& lseg(h, to, vs);

// Fixpoint to check if a list is sorted in non-decreasing order
fixpoint bool is_le(int x, int y) { return x <= y; }

fixpoint bool sorted(list<int> vs) {
    switch (vs) {
        case nil: return true;
        case cons(h, t): return forall(t, (is_le)(h)) && sorted(t);
    }
}

// Fixpoints and lemmas for proving permutation properties
fixpoint list<t> remove_one<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return h == x ? t : cons(h, remove_one(x, t));
    }
}

fixpoint bool is_permutation<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return ys == nil;
        case cons(h, t): return mem(h, ys) && is_permutation(t, remove_one(h, ys));
    }
}

lemma void is_permutation_refl<t>(list<t> xs);
    requires true;
    ensures is_permutation(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            is_permutation_refl(t);
    }
}

lemma void is_permutation_mem<t>(t x, list<t> xs, list<t> ys);
    requires is_permutation(xs, ys) == true;
    ensures mem(x, xs) == mem(x, ys);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (x == h) {
                assert mem(h, ys) == true;
            } else {
                assert mem(h, ys) == true;
                is_permutation_mem(x, t, remove_one(h, ys));
            }
    }
}

lemma void is_permutation_trans<t>(list<t> xs, list<t> ys, list<t> zs);
    requires is_permutation(xs, ys) == true &*& is_permutation(ys, zs) == true;
    ensures is_permutation(xs, zs) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_permutation_mem(h, ys, zs);
            is_permutation_trans(t, remove_one(h, ys), remove_one(h, zs));
    }
}

lemma void is_permutation_swap<t>(t x, t y, list<t> zs);
    requires true;
    ensures is_permutation(cons(x, cons(y, zs)), cons(y, cons(x, zs))) == true;
{
    is_permutation_refl(cons(x,zs));
    is_permutation_refl(cons(y,zs));
    is_permutation_refl(zs);
}

lemma void is_permutation_cons<t>(t h, list<t> xs, list<t> ys);
    requires is_permutation(xs, ys) == true;
    ensures is_permutation(cons(h, xs), cons(h, ys)) == true;
{
    switch (xs) {
        case nil:
        case cons(xh, xt):
            is_permutation_mem(xh, ys, ys);
            is_permutation_cons(h, xt, remove_one(xh, ys));
    }
}

lemma void is_permutation_append_r<t>(list<t> zs, list<t> xs, list<t> ys);
    requires is_permutation(xs, ys) == true;
    ensures is_permutation(append(zs, xs), append(zs, ys)) == true;
{
    switch(zs) {
        case nil:
        case cons(h, t):
            is_permutation_append_r(t, xs, ys);
            is_permutation_cons(h, append(t, xs), append(t, ys));
    }
}

fixpoint list<int> insert_sorted(int x, list<int> xs) {
    switch (xs) {
        case nil: return cons(x, nil);
        case cons(h, t): return x <= h ? cons(x, xs) : cons(h, insert_sorted(x, t));
    }
}

lemma void permutation_insert_sorted(int x, list<int> xs);
    requires true;
    ensures is_permutation(cons(x, xs), insert_sorted(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (x <= h) {
                is_permutation_refl(cons(x, xs));
            } else {
                permutation_insert_sorted(x, t);
                is_permutation_cons(h, cons(x, t), insert_sorted(x, t));
                is_permutation_swap(x, h, t);
                is_permutation_trans(cons(x, cons(h, t)), cons(h, cons(x, t)), cons(h, insert_sorted(x, t)));
            }
    }
}

lemma_auto void forall_mem<t>(fixpoint(t, bool) p, list<t> xs);
    requires forall(xs, p) == true &*& mem(?x, xs) == true;
    ensures p(x) == true;

lemma void sorted_insert_sorted(int x, list<int> xs);
    requires sorted(xs) == true;
    ensures sorted(insert_sorted(x, xs)) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (x <= h) {
                forall_mem((is_le)(h), t);
                assert forall(t, (is_le)(x)) == true;
            } else {
                sorted_insert_sorted(x, t);
            }
    }
}

fixpoint int last(list<int> xs) {
    switch(xs) {
        case cons(h, t): return t == nil ? h : last(t);
        case nil: return 0;
    }
}

lemma void sorted_append(list<int> xs, list<int> ys);
    requires sorted(xs) == true &*& sorted(ys) == true &*& (xs == nil || ys == nil || last(xs) <= head(ys));
    ensures sorted(append(xs, ys)) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (t == nil) {
                assert forall(ys, (is_le)(h)) == true;
            } else {
                sorted_append(t, ys);
            }
    }
}

lemma void lseg_p_split(struct list_node** pp, struct list_node* end)
    requires lseg_p(pp, end, ?vs) &*& vs != nil;
    ensures pointer(pp, ?h) &*& list_node(h, ?v, ?next) &*& lseg_p(&(h->next), end, ?tail) &*& vs == cons(v, tail);
{
    open lseg_p(pp, end, vs);
    open lseg(*pp, end, vs);
    close lseg_p(&(h->next), end, tail);
}

lemma void lseg_p_unsplit(struct list_node** pp, struct list_node* end)
    requires pointer(pp, ?h) &*& list_node(h, ?v, ?next) &*& lseg_p(&(h->next), end, ?tail);
    ensures lseg_p(pp, end, cons(v, tail));
{
    open lseg_p(&(h->next), end, tail);
    close lseg(h, end, cons(v, tail));
    close lseg_p(pp, end, cons(v, tail));
}

@*/

/***
 * Description:
The compare function compares the integer values of two linked list nodes.

@param n0 - pointer to the first node.
@param n1 - pointer to the second node.
@return -1 if n0's value < n1's value,
 *          1 if n0's value > n1's value,
 *          0 if equal.

It also makes sure that the values of the nodes are not modified during comparison.
*/
static int compare(struct list_node* n0, struct list_node* n1)
    //@ requires [?f0]n0->value |-> ?v0 &*& [?f1]n1->value |-> ?v1;
    //@ ensures [f0]n0->value |-> v0 &*& [f1]n1->value |-> v1 &*& result == (v0 < v1 ? -1 : (v0 > v1 ? 1 : 0));
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}


// TODO: make this function pass the verification
/***
 * Description:
The insertion_sort_core function performs an in-place insertion sort on a singly linked list.

It maintains a sorted portion of the list and iteratively inserts the next unsorted node 
into the correct position within the sorted portion.

@param pfirst - double pointer to the head of the list.
 *              Used for efficient node insertion at the head or interior.

It makes sure that after the sort, pfirst still points to the head of a list.
*/
void insertion_sort_core(struct list_node** pfirst)
    //@ requires pointer(pfirst, ?head) &*& lseg(head, 0, ?values);
    //@ ensures pointer(pfirst, ?new_head) &*& lseg(new_head, 0, ?new_values) &*& sorted(new_values) == true &*& is_permutation(values, new_values) == true;
{
    //@ open lseg(head, 0, values);
    if (*pfirst == 0) {
        //@ close lseg(0, 0, nil);
        //@ is_permutation_refl(nil);
        return;
    }
    
    //@ struct list_node* head_node = *pfirst;
    //@ list<int> tail_values = tail(values);
    //@ close lseg_p(&(head_node->next), 0, tail_values);
    struct list_node* last_sorted = *pfirst;
    
    while (last_sorted->next != 0)
        /*@
        invariant lseg_p(pfirst, last_sorted, ?sorted_vals) &*&
                    list_node(last_sorted, ?v_ls, ?f_unsorted) &*&
                    lseg(f_unsorted, 0, ?unsorted_vals) &*&
                    sorted(sorted_vals) == true &*&
                    is_permutation(append(sorted_vals, cons(v_ls, unsorted_vals)), values) == true;
        @*/
    {
        //@ open list_node(last_sorted, v_ls, f_unsorted);
        //@ struct list_node* node_to_insert = f_unsorted;
        //@ open lseg(node_to_insert, 0, unsorted_vals);
        //@ int v_nti = head(unsorted_vals);
        //@ struct list_node* rest_unsorted = node_to_insert->next;
        //@ list<int> rest_u_vals = tail(unsorted_vals);

        struct list_node** pn = pfirst;
        //@ list<int> prefix_vals = nil;
        //@ list<int> middle_vals = sorted_vals;
        
        int comparison = compare(*pn, last_sorted->next);
        
        while (pn != &(last_sorted->next) && comparison < 0)
            /*@
            invariant lseg_p(pfirst, *pn, prefix_vals) &*&
                        lseg_p(pn, last_sorted, middle_vals) &*&
                        list_node(last_sorted, v_ls, node_to_insert) &*&
                        list_node(node_to_insert, v_nti, rest_unsorted) &*&
                        lseg(rest_unsorted, 0, rest_u_vals) &*&
                        sorted_vals == append(prefix_vals, middle_vals) &*&
                        sorted(sorted_vals) == true &*&
                        forall(prefix_vals, (is_le)(v_nti)) == true &*&
                        is_permutation(append(sorted_vals, cons(v_ls, cons(v_nti, rest_u_vals))), values) == true &*&
                        (pn == &(last_sorted->next) || v_nti >= head(middle_vals));
            @*/
        {
            //@ lseg_p_split(pn, last_sorted);
            //@ struct list_node* curr = *pn;
            //@ int v_curr = head(middle_vals);
            //@ prefix_vals = append(prefix_vals, cons(v_curr, nil));
            //@ middle_vals = tail(middle_vals);
            pn = &((*pn)->next);
            //@ lseg_p_unsplit(pn, last_sorted);
            
            if (pn != &(last_sorted->next)) {
                comparison = compare(*pn, last_sorted->next);
            }
        }
        
        if (pn != &(last_sorted->next)) {
            struct list_node* first_unsorted = last_sorted->next;
            last_sorted->next = first_unsorted->next;
            first_unsorted->next = *pn;
            *pn = first_unsorted;
            
            //@ open lseg_p(pfirst, first_unsorted, _);
            //@ open lseg_p(pn, last_sorted, _);
            //@ list<int> new_sorted_part = insert_sorted(v_nti, sorted_vals);
            //@ permutation_insert_sorted(v_nti, sorted_vals);
            //@ is_permutation_append_r(cons(v_ls, rest_u_vals), cons(v_nti, sorted_vals), new_sorted_part);
            //@ sorted_insert_sorted(v_nti, sorted_vals);
            //@ close lseg_p(pfirst, last_sorted, new_sorted_part);
        } else {
            last_sorted = last_sorted->next;
            //@ list<int> new_sorted_vals = append(sorted_vals, cons(v_ls, nil));
            //@ sorted_append(sorted_vals, cons(v_ls, nil));
            //@ is_permutation_refl(append(new_sorted_vals, unsorted_vals));
            //@ close lseg_p(pfirst, last_sorted, new_sorted_vals);
        }
    }
    
    //@ open list_node(last_sorted, _, _);
    //@ open lseg_p(pfirst, last_sorted, ?final_sorted_vals);
    //@ open pointer(pfirst, ?new_head);
    //@ is_permutation_append_r(nil, append(final_sorted_vals, cons(last_sorted->value, nil)), append(final_sorted_vals, cons(last_sorted->value, nil)));
}