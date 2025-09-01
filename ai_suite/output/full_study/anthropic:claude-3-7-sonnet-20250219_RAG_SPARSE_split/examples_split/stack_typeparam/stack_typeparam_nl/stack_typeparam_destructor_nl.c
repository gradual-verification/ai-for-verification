#include "stdlib.h"
  
/*
  Destructors
*/

//@ predicate destructor_function(destructor *f) = is_destructor(f) == true;

// TODO: make this function pass the verification
/*
destructor function
-params: data
-description: It destructs the ownership on the location pointed by the data. It doesn't have a concrete implementation.
*/
typedef void destructor(void* data);
    //@ requires exists<void*>(?p) &*& p == data;
    //@ ensures true;


/*
  Stack
*/

struct node
{
  void* data;
  struct node* next;
};

//@ predicate node(struct node *n; void *data, struct node *next) = n->data |-> data &*& n->next |-> next &*& malloc_block_node(n);

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};

//@ predicate nodes(struct node *n, int count; list<void*> items) = n == 0 ? count == 0 &*& items == nil : node(n, ?data, ?next) &*& nodes(next, count - 1, ?tail) &*& items == cons(data, tail) &*& count > 0;

//@ predicate stack(struct stack *s; list<void*> items) = s->first |-> ?first &*& s->destructor |-> ?d &*& s->size |-> ?count &*& nodes(first, count, items) &*& destructor_function(d) &*& malloc_block_stack(s);

struct stack* create_stack(destructor* d)
    //@ requires destructor_function(d);
    //@ ensures stack(result, nil);
{
    struct stack* s = malloc(sizeof(struct stack));
    if (s == 0) abort();
    s->first = 0;
    s->destructor = d;
    s->size = 0;
    //@ close nodes(0, 0, nil);
    //@ close stack(s, nil);
    return s;
}

void stack_push(struct stack* s, void* data)
    //@ requires stack(s, ?items);
    //@ ensures stack(s, cons(data, items));
{
    //@ open stack(s, items);
    struct node* n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->data = data;
    n->next = s->first;
    s->first = n;
    s->size = s->size + 1;
    //@ close node(n, data, s->first);
    //@ close nodes(n, s->size, cons(data, items));
    //@ close stack(s, cons(data, items));
}

void* stack_pop(struct stack* s)
    //@ requires stack(s, ?items) &*& items != nil;
    //@ ensures stack(s, tail(items)) &*& result == head(items);
{
    //@ open stack(s, items);
    //@ open nodes(s->first, s->size, items);
    struct node* n = s->first;
    //@ open node(n, ?data, ?next);
    void* result = n->data;
    s->first = n->next;
    s->size = s->size - 1;
    free(n);
    //@ close stack(s, tail(items));
    return result;
}

void stack_dispose(struct stack* s)
    //@ requires stack(s, ?items);
    //@ ensures true;
{
    //@ open stack(s, items);
    struct node* n = s->first;
    destructor* d = s->destructor;
    int size = s->size;
    //@ close destructor_function(d);
    
    while (n != 0)
        //@ invariant nodes(n, size, ?remaining) &*& destructor_function(d) &*& size >= 0;
    {
        //@ open nodes(n, size, remaining);
        struct node* next = n->next;
        //@ open node(n, ?data, next);
        //@ close exists(data);
        d(n->data);
        free(n);
        n = next;
        size--;
    }
    //@ open nodes(0, 0, nil);
    free(s);
}

/*
  A few use cases
*/

struct data
{
  int foo;
  int bar;
};

//@ predicate data_struct(struct data *d; int foo, int bar) = d->foo |-> foo &*& d->bar |-> bar &*& malloc_block_data(d);

void dispose_data(void* data)
    //@ requires exists<void*>(?p) &*& p == data;
    //@ ensures true;
{
    struct data* d = (struct data*)data;
    //@ open exists(p);
    free(d);
}

int main() 
    //@ requires true;
    //@ ensures true;
{
    //@ close destructor_function(dispose_data);
    struct stack* s = create_stack(dispose_data);
    
    struct data* d1 = malloc(sizeof(struct data));
    if (d1 == 0) abort();
    d1->foo = 10;
    d1->bar = 20;
    //@ close data_struct(d1, 10, 20);
    
    stack_push(s, d1);
    
    struct data* d2 = malloc(sizeof(struct data));
    if (d2 == 0) abort();
    d2->foo = 30;
    d2->bar = 40;
    //@ close data_struct(d2, 30, 40);
    
    stack_push(s, d2);
    
    void* popped = stack_pop(s);
    struct data* d = (struct data*)popped;
    //@ open data_struct(d, 30, 40);
    assert(d->foo == 30);
    assert(d->bar == 40);
    free(d);
    
    stack_dispose(s);
    
    return 0;
}