```c
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

// Declaration of the arraylist structure
struct arraylist {
    void **data;
    int size;
    int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
    a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*&
    0 <= size &*& size <= capacity &*&
    data[0..size] |-> vs &*& data[size..capacity] |-> _ &*& malloc_block_arraylist(a) &*&
    malloc_block(data, capacity);
@*/

struct arraylist *create_arraylist() 
    //@ requires true;
    //@ ensures arraylist(result, nil);
{
    struct arraylist *a = malloc(sizeof(struct arraylist));
    if (a == 0) abort();
    a->size = 0;
    void *data = malloc(100 * sizeof(void*));
    if (data == 0) abort();
    a->data = data;
    a->capacity = 100;
    //@ close arraylist(a, nil);
    return a; 
}

void *list_get(struct arraylist *a, int i)
    //@ requires arraylist(a, ?vs) &*& i >= 0 &*& i < length(vs);
    //@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    //@ open arraylist(a, vs);
    return a->data[i];
    //@ close arraylist(a, vs);
}

int list_length(struct arraylist *a)
    //@ requires arraylist(a, ?vs);
    //@ ensures arraylist(a, vs) &*& result == length(vs);
{
    //@ open arraylist(a, vs);
    return a->size;
    //@ close arraylist(a, vs);
}

void list_add(struct arraylist *a, void *v)
    //@ requires arraylist(a, ?vs);
    //@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    int size = a->size;
    //@ open arraylist(a, vs);
    if (a->capacity <= a->size) {
        int capacity = a->capacity;
        void** data = a->data;
        if (SIZE_MAX / sizeof(void *) < (size_t)capacity * 2 + 1) abort();
        void** newData = malloc(((size_t)capacity * 2 + 1) * sizeof(void*));
        if (newData == 0) abort();
        memcpy(newData, data, (size_t)size * sizeof(void*));
        a->data = newData;
        if (INT_MAX / 2 - 1 < capacity) abort();
        a->capacity = capacity * 2 + 1;
        free(data);
    }
    a->data[size] = v;
    a->size += 1;
    //@ close arraylist(a, append(vs, cons(v, nil)));
}

void list_remove_nth(struct arraylist *a, int n)
    //@ requires arraylist(a, ?vs) &*& n >= 0 &*& n < length(vs);
    //@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
    void** data = a->data;
    int size = a->size;
    //@ open arraylist(a, vs);
    memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
    a->size = a->size - 1;
    //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}

void list_dispose(struct arraylist* a)
    //@ requires arraylist(a, ?vs);
    //@ ensures true;
{
    //@ open arraylist(a, vs);
    free(a->data);
    free(a);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct arraylist* a = create_arraylist();
    void* tmp = 0;
    list_add(a, (void *)10);
    list_add(a, (void *)20);
    
    tmp = list_get(a, 1);
    assert(tmp == (void*) 20);
    list_dispose(a);

    return 0;
}
```

### Notes:

1. **Predicate Structures**: The `arraylist` predicate is defined to track the data, size, and capacity of the arraylist while ensuring memory safety by asserting that the allocated sizes match expectations.
2. **Open/Close**: Used to manipulate the predicates at the beginning and end of functions to ensure correctness and reestablish invariants across updates.
3. **Loop Invariants**: Although not present here directly because functions use straight-line code, ensure that any loop that exists in an extended version correctly maintains its invariant.
4. **Memory Management**: Safety checks for memory allocation and ensuring allocated sizes align correctly help to prove memory safety.

This code with Verifast annotations will help ensure all specified conditions maintain memory safety, proper bounds checks, and logical consistency of the operations on the arraylist.
