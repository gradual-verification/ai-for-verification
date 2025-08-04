#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
    void ** data;
    int size;
    int capacity;
};

/*@
predicate malloc_block_arraylist(struct arraylist *a) =
    malloc_block(a, sizeof(struct arraylist));

predicate arraylist(struct arraylist *a; list<void*> vs) =
  a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*&
  malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _ &*&
  length(vs) == size;
@*/


// TODO: make this function pass the verification
void list_remove_nth(struct arraylist * a, int n)
//@ requires arraylist(a, ?vs) &*& 0 <= n &*& n < length(vs);
//@ ensures arraylist(a, append(take(n, vs), tail(drop(n, vs))));
{
    //@ open arraylist(a, vs);
    void ** data = a->data;
    int size = a->size;
    
    //@ list<void*> vs_take = take(n, vs);
    //@ list<void*> vs_drop = drop(n, vs);
    //@ list<void*> vs_tail_drop = tail(vs_drop);

    //@ assert data[0..size] |-> vs;
    //@ pointers_split(data, n);
    // Now have: data[0..n] |-> vs_take &*& data[n..size] |-> vs_drop
    
    //@ open pointers(data + n, size - n, vs_drop);
    // Now have: pointer(data + n, head(vs_drop)) &*& pointers(data + n + 1, size - n - 1, vs_tail_drop)
    
    // Prepare for memmove
    //@ pointer_to_chars(data + n);
    // Now have: chars((void*)(data + n), sizeof(void*), _)
    
    //@ pointers_to_chars(data + n + 1);
    // Now have: chars((void*)(data + n + 1), (size - n - 1) * sizeof(void*), ?cs_src)
    //       &*& pointers_of_chars(cs_src) == vs_tail_drop

    memmove(data + n, data + n + 1, (unsigned int)(size - n - 1) * sizeof(void * ));

    /*@
    // After memmove, we have:
    // chars((void*)(data + n), (size - n - 1) * sizeof(void*), cs_src)
    // chars((void*)(data + size - 1), sizeof(void*), _)
    
    // Convert back to pointers
    chars_to_pointers(data + n, size - n - 1);
    // Now have: pointers(data + n, size - n - 1, pointers_of_chars(cs_src))
    // Since we know pointers_of_chars(cs_src) == vs_tail_drop, we have:
    // pointers(data + n, size - n - 1, vs_tail_drop)
    
    // Convert the leftover part
    chars__to_pointers_(data + size - 1, 1);
    // Now have: pointers_(data + size - 1, 1, _)
    
    // Reassemble the main pointers chunk
    // We have:
    // 1. pointers(data, n, vs_take)
    // 2. pointers(data + n, size - n - 1, vs_tail_drop)
    pointers_join(data);
    // pointers(data, size - 1, append(vs_take, vs_tail_drop))
    
    list<void*> vs_new = append(vs_take, vs_tail_drop);
    
    // Reassemble the uninitialized parts
    // We have:
    // 1. pointers_(data + size - 1, 1, _)
    // 2. data[size..capacity] |-> _ which is pointers_(data + size, capacity - size, _)
    pointers__join(data + size - 1);
    // pointers_(data + size - 1, capacity - (size - 1), _)
    @*/

    a->size = a->size - 1;

    /*@
    // Check length of new list
    length_append(vs_take, vs_tail_drop);
    length_take(n, vs);
    length_tail(vs_drop);
    length_drop(n, vs);
    assert length(vs_new) == n + (length(vs_drop) - 1);
    assert length(vs_new) == n + (size - n - 1);
    assert length(vs_new) == size - 1;
    
    // Close the arraylist predicate
    close arraylist(a, vs_new);
    @*/
}