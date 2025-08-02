#include <stdlib.h>
#include <string.h>

// VeriFast includes
#include "stdlib.h"
#include "string.h"

// Define the struct_with_array structure
typedef struct {
    int x;
    int ar[7];
    int y;
} struct_with_array;

// Define the mystruct structure
struct mystruct {
    struct_with_array s1;
    int s2;
};

// Global variables
struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};
static int ar2[55];
static struct_with_array bigArray[10] = {{100, {1, 2, 3, 4}, 200}, {300, {5, 6, 7}, 400}};
struct point { int x; int y; };
struct point points[] = { { 10, 20 }, { 30, 40 } };

//@ predicate struct_with_array(struct_with_array *s; int x, list<int> ar, int y) =
//@     s->x |-> x &*& s->ar |-> ar &*& s->y |-> y &*& length(ar) == 7;

//@ predicate mystruct(struct mystruct *s; struct_with_array s1, int s2) =
//@     struct_with_array(&s->s1, ?x, ?ar, ?y) &*& s1 == (struct_with_array){x, ar, y} &*& s->s2 |-> s2;

//@ predicate points(struct point *p; int x, int y) =
//@     p->x |-> x &*& p->y |-> y;

//@ predicate points_array(struct point *p, int count; list<pair<int, int>> ps) =
//@     count == 0 ? ps == nil : points(p, ?x, ?y) &*& points_array(p + 1, count - 1, ?ps0) &*& ps == cons(pair(x, y), ps0);

//@ predicate bigArray_predicate(struct_with_array *arr, int count; list<struct_with_array> sas) =
//@     count == 0 ? sas == nil : struct_with_array(arr, ?x, ?ar, ?y) &*& bigArray_predicate(arr + 1, count - 1, ?sas0) &*& sas == cons((struct_with_array){x, ar, y}, sas0);

//@ predicate ar2_predicate(int *arr, int count; list<int> values) =
//@     count == 0 ? values == nil : integer(arr, ?v) &*& ar2_predicate(arr + 1, count - 1, ?vs0) &*& values == cons(v, vs0);

//@ predicate my_global_nested_struct_predicate(struct mystruct *s; struct_with_array s1, int s2) =
//@     mystruct(s, s1, s2);

//@ predicate my_local_nested_struct_predicate(struct mystruct *s; struct_with_array s1, int s2) =
//@     mystruct(s, s1, s2);

//@ predicate sh_predicate(struct mystruct *s; struct_with_array s1, int s2) =
//@     mystruct(s, s1, s2);

// foo() function
// TODO: make this function pass the verification
static void foo()
    //@ requires my_global_nested_struct_predicate(&my_global_nested_struct, ?s1, ?s2) &*& ar2_predicate(ar2, 55, ?ar2_values) &*& bigArray_predicate(bigArray, 10, ?bigArray_values) &*& points_array(points, 2, ?points_values);
    //@ ensures my_global_nested_struct_predicate(&my_global_nested_struct, s1, s2) &*& ar2_predicate(ar2, 55, ar2_values) &*& bigArray_predicate(bigArray, 10, bigArray_values) &*& points_array(points, 2, points_values);
{
    struct mystruct my_local_nested_struct;
    memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
    memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
    assert(&my_global_nested_struct != &my_local_nested_struct);
    struct mystruct *sh = malloc(sizeof(struct mystruct));
    if (sh == 0) abort();
    assert(sh != &my_global_nested_struct);
    assert(sh != &my_local_nested_struct);
    (&(&my_global_nested_struct)->s1)->ar[5] = 100;
    (&(&my_local_nested_struct)->s1)->ar[5] = 200;
    (&sh->s1)->ar[5] = 300;
    free(sh);
}