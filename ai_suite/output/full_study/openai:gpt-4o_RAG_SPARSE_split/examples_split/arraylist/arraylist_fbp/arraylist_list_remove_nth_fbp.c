#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
    void ** data;
    int size;
    int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/

// TODO: make this function pass the verification
void list_remove_nth(struct arraylist * a, int n)
//@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
    void ** data = a -> data;
    int size = a -> size;
    //@ open pointers(data, size, vs);
    //@ pointers_split(data, n);
    //@ pointers_split(data + n + 1, size - n - 1);
    memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void * ));
    //@ pointers_join(data + n);
    //@ pointers_join(data);
    a -> size = a -> size - 1;
    //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}