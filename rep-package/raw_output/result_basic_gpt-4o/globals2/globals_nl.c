#include "stdlib.h"

// Global variable
static int x;

// Structure definition
struct counter {
    int f;
};

// Global pointer to the structure
static struct counter *c;

/*@ 
predicate counter(struct counter *ctr, int f) =
    ctr != 0 &*& ctr->f |-> f &*& malloc_block_counter(ctr);
*/

/*@
  requires x |-> ?old_x &*& counter(c, ?old_f);
  ensures x |-> old_x + 1 &*& counter(c, old_f + 1);
*/
void m()
{
    int y = x;
    x = y + 1;
    c->f = c->f + 1;
}

/*@
  requires true;
  ensures result == 0;
*/
int main()
{
    x = 7;
    
    struct counter *ctr = malloc(sizeof(struct counter));
    if (ctr == 0) abort();
    
    ctr->f = 42;
    c = ctr;
    
    //@ close counter(c, 42);
    m();
    
    int ctr_f = ctr->f;
    assert(ctr_f == 43);
    
    //@ open counter(c, 43);
    free(ctr);
    
    return 0;
}
