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
// Predicate family to abstractly represent the memory footprint and value of a key.
// An implementation of equalsFuncType must provide an instance of this family.
// `p` is the function pointer of the specific equals implementation.
// `key` is the C-level pointer to the key data.
// `v` is the abstract value of the key. The type of `v` is `any` here,
// and will be concretized in the predicate family instance.
predicate_family key_value(void *p)(void *key, any v);

// Predicate family to specify the equality relation on abstract key values.
// An implementation of equalsFuncType must provide an instance of this family.
// `p` is the function pointer of the specific equals implementation.
// `v1` and `v2` are the abstract values to compare.
// `result` is the boolean result of the comparison.
predicate_family key_eq(void *p)(any v1, any v2, bool result);
@*/

// TODO: make this function pass the verification
/**
 * Description:
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);
    //@ requires key_value(this)(key, ?v1) &*& key_value(this)(key0, ?v2);
    //@ ensures key_value(this)(key, v1) &*& key_value(this)(key0, v2) &*& key_eq(this)(v1, v2, result);
