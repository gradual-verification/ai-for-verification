#include "stdlib.h"

struct pair {
    int x;
    int y;
};

/*@
predicate pair(struct pair *p, int x, int y) =
    malloc_block_pair(p) &*&                    // memory block returned by malloc
    p->x |-> x &*&                             // field permissions
    p->y |-> y;
@*/

/*----------------------------------------------------------*/
/* Constructors, mutators, accessors                        */
/*----------------------------------------------------------*/

struct pair* create_pair(int x, int y)
    //@ requires true;
    //@ ensures  pair(result, x, y);
{
    struct pair *p = malloc(sizeof(struct pair));
    if (p == 0) abort();

    /* we still own the raw bytes returned by malloc;                      *
     * we may simply initialise the fields and then close the predicate.   */
    p->x = x;
    p->y = y;
    //@ close pair(p, x, y);
    return p;
}

void update_pair(struct pair *p, int new_x, int new_y)
    //@ requires pair(p, _, _);
    //@ ensures  pair(p, new_x, new_y);
{
    //@ open pair(p, _, _);
    p->x = new_x;
    p->y = new_y;
    //@ close pair(p, new_x, new_y);
}

struct pair* copy_pair(struct pair *p)
    //@ requires pair(p, ?x, ?y);
    //@ ensures  pair(p,  x, y) &*&  pair(result, x, y);
{
    //@ open pair(p, x, y);
    struct pair *np = malloc(sizeof(struct pair));
    if (np == 0) abort();

    /* we are allowed to read p->x and p->y because the predicate           *
     * has been opened, so we own the field chunks.                         */
    np->x = p->x;
    np->y = p->y;

    //@ close pair(p,  x, y);
    //@ close pair(np, x, y);
    return np;
}

/*----------------------------------------------------------*/
/* Destructor                                               */
/*----------------------------------------------------------*/

void dispose_pair(struct pair *p)
    //@ requires pair(p, _, _);
    //@ ensures  true;
{
    //@ open pair(p, ?x, ?y);

    /* convert the two integer-field chunks to char-chunks so that          *
     * they match the footprint expected by free().                        */
    //@ integer_to_chars(&(p->x));
    //@ integer_to_chars(&(p->y));
    //@ chars_join((char *)&(p->x));                // merge the two parts

    free(p);                                      // consumes malloc_block + chars_
}

/*----------------------------------------------------------*/
/* Client – now fully verified                              */
/*----------------------------------------------------------*/

// TODO: make this function pass the verification
int main()
    //@ requires true;
    //@ ensures  true;
{
    struct pair *p      = create_pair(1, 2);      // pair(p,1,2)
    update_pair(p, 3, 4);                         // pair(p,3,4)

    struct pair *p_copy = copy_pair(p);           // pair(p,3,4) & pair(p_copy,3,4)

    dispose_pair(p);                              // consumes first predicate
    dispose_pair(p_copy);                         // consumes second predicate

    return 0;
}