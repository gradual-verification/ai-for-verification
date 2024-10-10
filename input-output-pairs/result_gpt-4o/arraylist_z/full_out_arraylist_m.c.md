```c
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "arraylist.h"

struct arraylist {
    void **data;
    int size;
    int capacity;
};

/*@
predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;
@*/

struct arraylist *create_arraylist()
//@ requires true;
//@ ensures arraylist(result, nil);
{
    struct arraylist *a = malloc(sizeof(struct arraylist));
    if (a == 0) abort();
    a->size = 0;
    void *data = malloc(100 * sizeof(void *));
    if (data == 0) abort();
    a->data = data;
    a->capacity = 100;
    return a;
}

void *list_get(struct arraylist *a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    return a->data[i];
}

int list_length(struct arraylist *a)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, vs) &*& result == length(vs);
{
    return a->size;
}

void list_add(struct arraylist *a, void *v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    int size = a->size;
    if (a->capacity <= a->size) {
        void **data = a->data;
        int capacity = a->capacity;
        if (SIZE_MAX / sizeof(void *) < capacity * 2 + 1) abort();
        void **newData = malloc((capacity * 2 + 1) * sizeof(void *));
        if (newData == 0) abort();
        memcpy(newData, data, size * sizeof(void *));
        a->data = newData;
        a->capacity = capacity * 2 + 1;
        free(data);
    }
    a->data[size] = v;
    a->size += 1;
}

void list_remove_nth(struct arraylist *a, int n)
//@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
    void **data = a->data;
    int size = a->size;
    memmove(data + n, data + n + 1, (size - n - 1) * sizeof(void *));
    a->size -= 1;
}

void list_dispose(struct arraylist *a)
//@ requires arraylist(a, ?vs);
//@ ensures true;
{
    free(a->data);
    free(a);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct arraylist *a = create_arraylist();
    list_add(a, (void *)10);
    list_add(a, (void *)20);

    void *tmp = list_get(a, 1);
    assert(tmp == (void *)20);

    list_dispose(a);
    return 0;
}
```

This code has been augmented with Verifast annotations (`//@`) to verify the correctness of the list operations, ensuring the necessary preconditions and postconditions are met for each function and asserting the functional behavior in the `main()` function.
