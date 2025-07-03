#include <stdlib.h>

struct node {
    struct node *next;
    int value;
};

struct list {
    struct node *head;
};

/*@
predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*& from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*&
        lseg(next, to, ?nvs) &*& vs == cons(val, nvs);

predicate list(struct list *l, list<int> vs) =
    l->head |-> ?head &*& malloc_block_list(l) &*& lseg(head, 0, vs);
@*/

// TODO: make this function pass the verification
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
    n->next = l->head;
    n->value = x;
    l->head = n;
    //@ close lseg(n, 0, cons(x, nil));
    //@ close list(l, cons(x, vs));
}

int list_length(struct list *l)
    //@ requires list(l, ?vs);
    //@ ensures list(l, vs) &*& result == length(vs);
{
    //@ open list(l, vs);
    struct node *current = l->head;
    int length = 0;
    while (current != 0)
        //@ invariant lseg(current, 0, ?vs0) &*& length == length(vs0);
    {
        //@ open lseg(current, 0, vs0);
        length++;
        current = current->next;
    }
    //@ close lseg(0, 0, nil);
    //@ close list(l, vs);
    return length;
}

void dispose(struct list *l)
    //@ requires list(l, ?vs);
    //@ ensures true;
{
    //@ open list(l, vs);
    struct node *current = l->head;
    while (current != 0)
        //@ invariant lseg(current, 0, ?vs0);
    {
        //@ open lseg(current, 0, vs0);
        struct node *oldcurrent = current;
        current = current->next;
        free(oldcurrent);
    }
    //@ open lseg(0, 0, nil);
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
    int len = list_length(l);
    //@ assert len == 3;
    dispose(l);
    return 0;
}