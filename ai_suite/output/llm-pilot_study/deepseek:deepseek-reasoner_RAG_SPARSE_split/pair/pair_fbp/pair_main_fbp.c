#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate malloc_block_pair(struct pair *p) = malloc_block(p, sizeof(struct pair));

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
    //@ close pair(p, x, y);
    return p;
}

void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures pair(p, new_x, new_y);
{
    //@ open pair(p, _, _);
    p->x = new_x;
    p->y = new_y;
    //@ close pair(p, new_x, new_y);
}

struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures pair(p, x, y) &*& pair(result, x, y);
{
    struct pair* new_p = malloc(sizeof(struct pair));
    if (new_p == 0) abort();
    new_p->x = p->x;
    new_p->y = p->y;
    //@ close pair(new_p, x, y);
    return new_p;
}

void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures true;
{
    //@ open pair(p, _, _);
    free(p);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct pair* p = create_pair(1, 2);
    update_pair(p, 3, 4);
    
    struct pair* p_copy = copy_pair(p);
    
    dispose_pair(p);
    dispose_pair(p_copy);
    
    return 0;
}