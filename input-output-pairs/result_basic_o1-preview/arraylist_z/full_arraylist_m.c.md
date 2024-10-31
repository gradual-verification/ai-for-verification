```c
#include <stdlib.h>

/*@
predicate arraylist(struct arraylist *a; list<int> vs) =
    a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity
    &*& malloc_block_arraylist(a)
    &*& 0 <= size &*& size <= capacity
    &*& ints(data, capacity, ?elems)
    &*& vs == take(size, elems);
@*/

struct arraylist {
    int * data;
    int size;
    int capacity;
};

struct arraylist * create_arraylist()
//@ requires true;
//@ ensures arraylist(result, nil);
{
    struct arraylist * a = malloc(sizeof(struct arraylist));
    if (a == 0) abort();
    a->size = 0;
    a->capacity = 100;
    int * data = malloc(100 * sizeof(int));
    if (data == 0) abort();
    a->data = data;
    //@ ints(data, a->capacity, _);
    //@ close arraylist(a, nil);
    return a;
}

void list_add(struct arraylist * a, int v)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, append(vs, cons(v, nil)));
{
    if (a->capacity <= a->size) {
        int capacity = a->capacity;
        int size = a->size;
        int * data = a->data;
        if (SIZE_MAX / sizeof(int) < (size_t) capacity * 2 + 1) abort();
        int * newData = malloc(((size_t) capacity * 2 +1) * sizeof(int));
        if (newData == 0) abort();
        memcpy(newData, data, (size_t) size * sizeof(int));
        free(data);
        //@ ints(data, capacity, ?elems);
        //@ ints(newData, capacity * 2 + 1, _);
        a->data = newData;
        a->capacity = capacity * 2 + 1;
        //@ close ints(newData, size, take(size, elems));
        //@ close ints(newData + size, a->capacity - size, _);
    }
    int size = a->size;
    int * data = a->data;
    data[size] = v;
    a->size +=1;
    //@ ints(data, a->capacity, ?elems);
    //@ elems_new = update_nth(size, elems, v);
    //@ close ints(data, a->capacity, elems_new);
    //@ close arraylist(a, append(vs, cons(v, nil)));
}

int list_get(struct arraylist * a, int i)
//@ requires arraylist(a, ?vs) &*& 0 <= i &*& i < length(vs);
//@ ensures arraylist(a, vs) &*& result == nth(i, vs);
{
    //@ open arraylist(a, vs);
    int result = a->data[i];
    //@ close arraylist(a, vs);
    return result;
}

int list_length(struct arraylist * a)
//@ requires arraylist(a, ?vs);
//@ ensures arraylist(a, vs) &*& result == length(vs);
{
    return a->size;
}

void list_remove_nth(struct arraylist * a, int n)
//@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
    int * data = a->data;
    int size = a->size;
    memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(int));
    a->size = a->size -1;
    //@ ints(data, a->capacity, ?elems);
    //@ elems_new = remove_nth(elems, n);
    //@ close ints(data, a->capacity, elems_new);
    //@ close arraylist(a, append(take(n, vs), tail(drop(n, vs))));
}

void list_dispose(struct arraylist * a)
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
    struct arraylist * a = create_arraylist();
    list_add(a, 10);
    list_add(a, 20);
    int tmp = list_get(a, 1);
    //@ assert(tmp == 20);
    list_dispose(a);
    return 0;
}
```
