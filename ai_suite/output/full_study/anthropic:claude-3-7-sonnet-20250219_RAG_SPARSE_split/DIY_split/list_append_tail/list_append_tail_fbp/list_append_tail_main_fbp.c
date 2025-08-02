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
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
    //@ close llist(0);
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
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        //@ open lseg(curr, 0);
        
        if (curr->next == 0) {
            curr->next = new_node;
            //@ close lseg(curr, 0);
            //@ close llist(head);
            return head;
        } else {
            struct node *tmp = curr;
            curr = curr->next;
            
            /*@
            lemma void lseg_add_tail(struct node *from, struct node *to, struct node *tail)
                requires lseg(from, to) &*& lseg(tail, 0);
                ensures lseg(from, 0) &*& to->next |-> tail;
            {
                open lseg(from, to);
                if (from == to) {
                    open lseg(tail, 0);
                } else {
                    if (from->next == to) {
                        from->next = tail;
                    } else {
                        lseg_add_tail(from->next, to, tail);
                    }
                }
            }
            @*/
            
            while (curr->next != 0)
                //@ invariant lseg(head, tmp) &*& tmp->next |-> curr &*& lseg(curr, 0);
            {
                tmp = curr;
                curr = curr->next;
                //@ open lseg(curr, 0);
            }
            curr->next = new_node;
            //@ close lseg(curr, 0);
            //@ close llist(head);
            return head;
        }
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
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
    //@ close lseg(0, 0);
    //@ close llist(0);
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
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        
        /*@
        lemma void lseg_append_lemma(struct node *from, struct node *to, struct node *tail)
            requires lseg(from, to) &*& lseg(tail, 0) &*& to != 0;
            ensures lseg(from, 0) &*& to->next |-> tail;
        {
            open lseg(from, to);
            if (from == to) {
                // Base case: from == to
            } else {
                // Recursive case
                if (from->next == to) {
                    // Direct connection
                    close lseg(tail, 0);
                } else {
                    // Need to recurse deeper
                    lseg_append_lemma(from->next, to, tail);
                    close lseg(from, 0);
                }
            }
        }
        @*/
        
        while (curr->next != 0)
            //@ invariant lseg(curr, 0);
        {
            //@ open lseg(curr, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp, curr);
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ close lseg(curr, 0);
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
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
    //@ close lseg(0, 0);
    //@ close llist(0);
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
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        
        /*@
        lemma void lseg_split(struct node *from, struct node *mid)
            requires lseg(from, 0) &*& from != 0;
            ensures lseg(from, mid) &*& lseg(mid, 0);
        {
            open lseg(from, 0);
            if (from->next == 0) {
                mid = 0;
                close lseg(from, mid);
                close lseg(mid, 0);
            } else {
                struct node *next = from->next;
                lseg_split(next, mid);
                close lseg(from, mid);
            }
        }
        @*/
        
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& lseg(curr, 0);
        {
            //@ open lseg(curr, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp, curr);
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ close lseg(curr, 0);
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
@*/

struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    return 0;
    //@ close lseg(0, 0);
    //@ close llist(0);
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
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        
        // Find the last node
        while (curr->next != 0)
            /*@ invariant curr != 0 &*& malloc_block_node(curr) &*& 
                         curr->next |-> ?next &*& lseg(next, 0); @*/
        {
            curr = curr->next;
            //@ open lseg(curr, 0);
        }
        
        curr->next = new_node;
        //@ close lseg(curr->next, 0);
        //@ close lseg(head, 0);
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