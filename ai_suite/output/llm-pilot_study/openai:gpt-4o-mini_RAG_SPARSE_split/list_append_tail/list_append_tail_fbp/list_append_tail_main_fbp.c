#include <stdlib.h>

struct node {
    struct node *next;
    int value;
};

struct list {
    struct node *head;
};

/*@
predicate lseg(struct node *from, struct node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*& from->value |-> ?value &*& from->next |-> ?next &*& malloc_block_node(from) &*&
        lseg(next, to, ?nvs) &*& vs == cons(value, nvs);

predicate list(struct list *l; list<int> vs) =
    l->head |-> ?head &*& malloc_block_list(l) &*& lseg(head, 0, vs);
@*/

struct list *create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
    struct list *l = malloc(sizeof(struct list));
    if (l == 0) { abort(); }
    l->head = 0;
    //@ close lseg(0, 0, nil);
    //@ close list(l, nil);
    return l;
}

void add(struct list *l, int x)
    //@ requires list(l, ?vs);
    //@ ensures list(l, cons(x, vs));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->value = x;
    n->next = l->head;
    l->head = n;
}

int list_length(struct list *l)
    //@ requires list(l, ?vs);
    //@ ensures list(l, vs) &*& result == length(vs);
{
    //@ open list(l, vs);
    int length = list_length_helper(l->head);
    //@ close list(l, vs);
    return length;
}

int list_length_helper(struct node *n)
    //@ requires lseg(n, 0, ?vs);
    //@ ensures lseg(n, 0, vs) &*& result == length(vs);
{
    //@ open lseg(n, 0, vs);
    if (n == 0) {
        //@ close lseg(0, 0, nil);
        return 0;
    } else {
        int length = list_length_helper(n->next);
        //@ close lseg(n, 0, vs);
        return length + 1;
    }
}

void dispose(struct list *l)
    //@ requires list(l, _);
    //@ ensures true;
{
    //@ open list(l, _);
    struct node *current = l->head;
    while (current != 0)
        //@ invariant lseg(current, 0, _);
    {
        //@ open lseg(current, 0, _);
        struct node *oldcurrent = current;
        current = current->next;
        free(oldcurrent);
    }
    //@ open lseg(0, 0, _);
    free(l);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct list *l = create_list();
    add(l, 1);
    add(l, 2);
    add(l, 3);
    add(l, 4);

    int length = list_length(l);
    //@ assert length == 4;

    dispose(l);
    return 0;
}