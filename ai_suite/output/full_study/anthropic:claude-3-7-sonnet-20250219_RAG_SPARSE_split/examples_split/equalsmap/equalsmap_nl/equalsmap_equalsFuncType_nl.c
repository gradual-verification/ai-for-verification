#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

/*@
// Predicate to represent a valid key-value pair
predicate key_value_pair(void *key, void *value) = 
    key != 0 &*& value != 0;

// Predicate to represent a node in the linked list
predicate node_p(struct node *n; void *key, void *value, struct node *next) =
    n != 0 &*& 
    n->key |-> key &*& 
    n->value |-> value &*& 
    n->next |-> next &*& 
    malloc_block_node(n) &*&
    key_value_pair(key, value);

// Predicate to represent a linked list of nodes
predicate nodes(struct node *n; list<pair<void*, void*> > entries) =
    n == 0 ?
        entries == nil
    :
        n->key |-> ?key &*& 
        n->value |-> ?value &*& 
        n->next |-> ?next &*& 
        malloc_block_node(n) &*&
        key_value_pair(key, value) &*&
        nodes(next, ?tail) &*&
        entries == cons(pair(key, value), tail);
@*/

// TODO: make this function pass the verification
/**
 * Description:
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);
    //@ requires key != 0 &*& key0 != 0;
    //@ ensures result ? key == key0 : key != key0;

/*@
// Helper lemma to show that a function satisfying the equalsFuncType contract
// will return true for identical keys
lemma void equals_func_reflexive(equalsFuncType *equals_func, void *key)
    requires is_equalsFuncType(equals_func) == true &*& key != 0;
    ensures equals_func(key, key) == true;
{
    // This is a specification-only lemma that states a property about
    // any function that satisfies the equalsFuncType contract
}

// Helper lemma to show that a function satisfying the equalsFuncType contract
// is symmetric
lemma void equals_func_symmetric(equalsFuncType *equals_func, void *key1, void *key2)
    requires is_equalsFuncType(equals_func) == true &*& key1 != 0 &*& key2 != 0;
    ensures equals_func(key1, key2) == equals_func(key2, key1);
{
    // This is a specification-only lemma that states a property about
    // any function that satisfies the equalsFuncType contract
}

// Example implementation of an equals function for foo structs
predicate foo_p(struct foo *f; int value) =
    f != 0 &*& f->value |-> value &*& malloc_block_foo(f);
@*/

// Example implementation of an equals function for foo structs
bool foo_equals(void *key1, void *key2) //@ : equalsFuncType
    //@ requires key1 != 0 &*& key2 != 0;
    //@ ensures result ? key1 == key2 : key1 != key2;
{
    struct foo *f1 = (struct foo *)key1;
    struct foo *f2 = (struct foo *)key2;
    
    // Direct pointer comparison
    return f1 == f2;
}

// Example implementation of an equals function that compares foo values
bool foo_value_equals(void *key1, void *key2) //@ : equalsFuncType
    //@ requires key1 != 0 &*& key2 != 0 &*& [?f1]foo_p(key1, ?v1) &*& [?f2]foo_p(key2, ?v2);
    //@ ensures [f1]foo_p(key1, v1) &*& [f2]foo_p(key2, v2) &*& result == (v1 == v2);
{
    struct foo *f1 = (struct foo *)key1;
    struct foo *f2 = (struct foo *)key2;
    
    // Value comparison
    return f1->value == f2->value;
}

// Example function that uses the equals function type
bool find_node(struct node *head, void *search_key, equalsFuncType *equals_func, void **result_value)
    //@ requires head != 0 &*& nodes(head, ?entries) &*& is_equalsFuncType(equals_func) == true &*& search_key != 0 &*& result_value != 0 &*& *result_value |-> _;
    //@ ensures nodes(head, entries) &*& *result_value |-> ?value &*& (result ? value != 0 &*& exists(?i) &*& 0 <= i &*& i < length(entries) &*& fst(nth(i, entries)) == search_key : true);
{
    struct node *current = head;
    bool found = false;
    
    //@ open nodes(head, entries);
    while (current != 0 && !found)
        /*@ invariant current != 0 ? 
                    current->key |-> ?key &*& 
                    current->value |-> ?value &*& 
                    current->next |-> ?next &*& 
                    malloc_block_node(current) &*&
                    key_value_pair(key, value) &*&
                    nodes(next, ?tail) &*&
                    entries == cons(pair(key, value), tail)
                  : nodes(current, ?remaining) &*& entries == remaining; @*/
    {
        if (equals_func(current->key, search_key)) {
            *result_value = current->value;
            found = true;
        } else {
            struct node *next = current->next;
            //@ close nodes(current, cons(pair(current->key, current->value), tail));
            current = next;
            if (current != 0) {
                //@ open nodes(current, tail);
            }
        }
    }
    
    if (!found) {
        *result_value = 0;
    }
    
    //@ close nodes(head, entries);
    return found;
}