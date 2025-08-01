#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*& p->x |-> x &*& p->y |-> y;
@*/

struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures pair(result, x, y);
{
    struct pair* p = malloc(sizeof(struct pair));
    if (p == 0) abort();
    p->x = x;
    p->y = y;
    return p;
}

void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures pair(p, new_x, new_y);
{
    p->x = new_x;
    p->y = new_y;
}

struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures pair(p, x, y) &*& pair(result, x, y);
{
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    return new_p;
}

void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures true;
{
    free(p);
}

// TODO: make this function pass the verification
int main()
    //@ requires true;z
    //@ ensures true;
{
    struct pair* p = create_pair(1, 2);
    //@ open pair(p, 1, 2);
    update_pair(p, 3, 4);
    //@ close pair(p, 3, 4);
    
    struct pair* p_copy = copy_pair(p);
    //@ open pair(p_copy, 3, 4);
    
    dispose_pair(p);
    dispose_pair(p_copy);
    
    return 0;
}