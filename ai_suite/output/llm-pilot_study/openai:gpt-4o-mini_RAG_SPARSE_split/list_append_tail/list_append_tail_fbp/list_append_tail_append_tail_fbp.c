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
    from == to ? vs == nil :
    from != 0 &*& from->next |-> ?next &*& from->value |-> ?val &*&
    malloc_block_node(from) &*& lseg(next, to, ?nextvs) &*& vs == cons(val, nextvs);

predicate list(struct list *l, list<int> vs) =
    l->head |-> ?head &*& lseg(head, 0, vs) &*& malloc_block_list(l);
@*/

// TODO: make this function pass the verification
struct list* create_list()
    //@ requires true;
    //@ ensures list(result, nil);
{
    struct list* l = malloc(sizeof(struct list));
    if (l == 0) return 0;
    l->head = 0;
    //@ close lseg(0, 0, nil);
    //@ close list(l, nil);
    return l;
}

// TODO: make this function pass the verification
void add(struct list* l, int x)
    //@ requires list(l, ?vs);
    //@ ensures list(l, cons(x, vs));
{
    struct node* n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = x;
    n->next = l->head;
    l->head = n;
    //@ close lseg(n, 0, cons(x, vs));
    //@ close list(l, cons(x, vs));
}

// TODO: make this function pass the verification
int list_length(struct list* l)
    //@ requires list(l, ?vs);
    //@ ensures list(l, vs) &*& result == length(vs);
{
    //@ open list(l, vs);
    int length = 0;
    struct node* current = l->head;
    while (current != 0)
        //@ invariant lseg(current, 0, ?current_vs) &*& length == length(current_vs) &*& vs == append(current_vs, tail(vs));
    {
        length++;
        current = current->next;
    }
    //@ close lseg(0, 0, nil);
    return length;
}

// TODO: make this function pass the verification
void dispose(struct list* l)
    //@ requires list(l, _);
    //@ ensures true;
{
    //@ open list(l, _);
    struct node* current = l->head;
    while (current != 0)
        //@ invariant lseg(current, 0, _);
    {
        struct node* tmp = current;
        current = current->next;
        free(tmp);
    }
    free(l);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct list* l = create_list();
    add(l, 1);
    add(l, 2);
    add(l, 3);
    
    int len = list_length(l);
    //@ assert len == 3;

    dispose(l);
    return 0;
}