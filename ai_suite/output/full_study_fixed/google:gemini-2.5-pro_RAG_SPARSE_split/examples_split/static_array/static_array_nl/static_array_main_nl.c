#include <stdlib.h>
#include <string.h>
#include <assert.h>

/*@
fixpoint list<t> repeat<t>(t v, int n) {
    return n <= 0 ? nil : cons(v, repeat(v, n - 1));
}
@*/

typedef struct
 {
  int x;
  int ar [7];
  int y;

 } struct_with_array;

/*@
predicate struct_with_array_components(struct_with_array *s; int x, list<int> ar_v, int y) =
    s->x |-> x &*&
    ints(s->ar, 7, ar_v) &*&
    s->y |-> y;

predicate struct_with_array_components_(struct_with_array *s; option<int> x, list<option<int>> ar_v, option<int> y) =
    s->x |-> ?x_val &*& x == some(x_val) &*&
    ints_(s->ar, 7, ar_v) &*&
    s->y |-> ?y_val &*& y == some(y_val);
@*/

struct mystruct {
  struct_with_array s1;
  int s2;
};

/*@
predicate mystruct_components(struct mystruct *s; int s1_x, list<int> s1_ar, int s1_y, int s2) =
    struct_with_array_components(&s->s1, s1_x, s1_ar, s1_y) &*&
    s->s2 |-> s2;

predicate mystruct_components_(struct mystruct *s;) =
    struct_with_array_components_(&s->s1, _, _, _) &*&
    s->s2 |-> _;
@*/

struct point { int x; int y; };

/*@
predicate point_components(struct point *p; int x, int y) =
    p->x |-> x &*&
    p->y |-> y;

predicate struct_with_array_arr(struct_with_array* arr, int count; list<pair<pair<int, list<int>>, int>> values) =
    count == 0 ?
        values == nil
    :
        struct_with_array_components(arr, ?x, ?ar, ?y) &*&
        struct_with_array_arr(arr + 1, count - 1, ?tail) &*&
        values == cons(pair(pair(x, ar), y), tail);

predicate point_arr(struct point* arr, int count; list<pair<int, int>> values) =
    count == 0 ?
        values == nil
    :
        point_components(arr, ?x, ?y) &*&
        point_arr(arr + 1, count - 1, ?tail) &*&
        values == cons(pair(x, y), tail);

// Predicates for global variables
predicate my_global_nested_struct_g(int s1_x, list<int> s1_ar, int s1_y, int s2) =
    mystruct_components(&my_global_nested_struct, s1_x, s1_ar, s1_y, s2);

predicate ar2_g(list<int> vs) =
    ints(ar2, 55, vs);

predicate bigArray_g(list<pair<pair<int, list<int>>, int>> values) =
    struct_with_array_arr(bigArray, 10, values);

predicate points_g(list<pair<int, int>> values) =
    point_arr(points, 2, values);

// Combined predicate for all globals
predicate world(
    int s1_x, list<int> s1_ar, int s1_y, int s2,
    list<int> ar2_vs,
    list<pair<pair<int, list<int>>, int>> bigArray_vs,
    list<pair<int, int>> points_vs
) =
    my_global_nested_struct_g(s1_x, s1_ar, s1_y, s2) &*&
    ar2_g(ar2_vs) &*&
    bigArray_g(bigArray_vs) &*&
    points_g(points_vs);

// Initial values for globals
fixpoint list<int> ar2_initial() { return repeat(0, 55); }
fixpoint list<pair<pair<int, list<int>>, int>> bigArray_initial() {
    return cons(pair(pair(100, cons(1, cons(2, cons(3, cons(4, repeat(0, 3)))))), 200),
           cons(pair(pair(300, cons(5, cons(6, cons(7, repeat(0, 4))))), 400),
           repeat(pair(pair(0, repeat(0, 7)), 0), 8)));
}
fixpoint list<pair<int, int>> points_initial() {
    return cons(pair(10, 20), cons(pair(30, 40), nil));
}

predicate static_array_main_nl() =
    world(
        42, cons(420, cons(421, cons(422, cons(423, cons(424, cons(425, cons(426, nil))))))), -3, -99,
        ar2_initial(),
        bigArray_initial(),
        points_initial()
    );

lemma void struct_with_array_to_chars_(struct_with_array *s)
    requires s->x |-> _ &*& ints_(s->ar, 7, _) &*& s->y |-> _;
    ensures chars_((void *)s, sizeof(struct_with_array), _);
{
    int__to_chars_(&s->x);
    ints__to_chars_(s->ar);
    int__to_chars_(&s->y);
    chars__join((void *)s);
    chars__join((void *)s);
}

lemma void chars_to_struct_with_array_(struct_with_array *s)
    requires chars_((void *)s, sizeof(struct_with_array), _);
    ensures s->x |-> _ &*& ints_(s->ar, 7, _) &*& s->y |-> _;
{
    chars__split((void *)s, sizeof(int));
    chars__split((void *)s + sizeof(int), 7 * sizeof(int));
    chars__to_int_(&s->x);
    chars__to_ints_(s->ar, 7);
    chars__to_int_(&s->y);
}

lemma void mystruct_to_chars_(struct mystruct *s)
    requires mystruct_components_(s);
    ensures chars_((void *)s, sizeof(struct mystruct), _);
{
    open mystruct_components_(s);
    open struct_with_array_components_(&s->s1, _, _, _);
    struct_with_array_to_chars_(&s->s1);
    int__to_chars_(&s->s2);
    chars__join((void *)s);
}

lemma void chars_to_mystruct_(struct mystruct *s)
    requires chars_((void *)s, sizeof(struct mystruct), _);
    ensures mystruct_components_(s);
{
    chars__split((void *)s, sizeof(struct_with_array));
    chars_to_struct_with_array_(&s->s1);
    close struct_with_array_components_(&s->s1, _, _, _);
    chars__to_int_(&s->s2);
    close mystruct_components_(s);
}

@*/

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static int ar2 [55];

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; // Incomplete initializer lists; remaining elements get default value.

struct point points[] = { { 10, 20 }, { 30, 40 } };


/*foo() function
-params: none
-description: This function checks if the global struct is different from the local structs.
It makes sure that my_global_nested_struct still keeps the structure of mystruct. 
*/
static void foo()
    //@ requires world(?s1_x, ?s1_ar, ?s1_y, ?s2, ?ar2_vs, ?bigArray_vs, ?points_vs);
    //@ ensures world(s1_x, update(5, 100, s1_ar), s1_y, s2, ar2_vs, bigArray_vs, points_vs);
{
    //@ open world(s1_x, s1_ar, s1_y, s2, ar2_vs, bigArray_vs, points_vs);
    //@ open my_global_nested_struct_g(s1_x, s1_ar, s1_y, s2);
    
    struct mystruct my_local_nested_struct;
    //@ mystruct_to_chars_(&my_local_nested_struct);
    memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
    
    //@ chars_split((void *)&my_local_nested_struct, sizeof(struct_with_array));
    //@ chars_to_struct_with_array_(&my_local_nested_struct.s1);
    //@ struct_with_array_to_chars_(&my_local_nested_struct.s1);
    memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
    //@ chars__join((void *)&my_local_nested_struct);
    
    assert(&my_global_nested_struct != &my_local_nested_struct);
    struct mystruct *sh = malloc(sizeof(struct mystruct));
    if (sh == 0) abort();
    assert(sh != &my_global_nested_struct);
    assert(sh != &my_local_nested_struct);
    
    //@ open mystruct_components(s1_x, s1_ar, s1_y, s2);
    //@ open struct_with_array_components(&my_global_nested_struct.s1, s1_x, s1_ar, s1_y);
    (&(&my_global_nested_struct)->s1)->ar[5] = 100;
    
    //@ chars_to_mystruct_(sh);
    //@ open mystruct_components_(sh);
    //@ open struct_with_array_components_(&sh->s1, _, _, _);
    //@ open ints_(sh->s1.ar, 7, _);
    (&sh->s1.ar)[5] = 300;
    //@ close ints_(sh->s1.ar, 7, _);
    //@ close struct_with_array_components_(&sh->s1, _, _, _);
    //@ close mystruct_components_(sh);
    
    //@ chars_to_mystruct_(&my_local_nested_struct);
    //@ open mystruct_components_(&my_local_nested_struct);
    //@ open struct_with_array_components_(&my_local_nested_struct.s1, _, _, _);
    //@ open ints_(my_local_nested_struct.s1.ar, 7, _);
    (&(&my_local_nested_struct)->s1)->ar[5] = 200;
    //@ close ints_(my_local_nested_struct.s1.ar, 7, _);
    //@ close struct_with_array_components_(&my_local_nested_struct.s1, _, _, _);
    //@ close mystruct_components_(&my_local_nested_struct);
    
    //@ mystruct_to_chars_(sh);
    free(sh);
    
    //@ close struct_with_array_components(&my_global_nested_struct.s1, s1_x, update(5, 100, s1_ar), s1_y);
    //@ close mystruct_components(&my_global_nested_struct, s1_x, update(5, 100, s1_ar), s1_y, s2);
    //@ close my_global_nested_struct_g(s1_x, update(5, 100, s1_ar), s1_y, s2);
    //@ close world(s1_x, update(5, 100, s1_ar), s1_y, s2, ar2_vs, bigArray_vs, points_vs);
}



/*mod_ar2() function
-params: none
-description: This function modifies a global array. 

It requires that the first and 26-th elements are in the range of 0 ~ 50.
It ensures that the first element is updated to the sum of the first and 26-th elements.
*/
void mod_ar2 (void)
    //@ requires world(?s1_x, ?s1_ar, ?s1_y, ?s2, ?ar2_vs, ?bigArray_vs, ?points_vs) &*& 0 <= nth(1, ar2_vs) &*& nth(1, ar2_vs) <= 50 &*& 0 <= nth(26, ar2_vs) &*& nth(26, ar2_vs) <= 50;
    //@ ensures world(s1_x, s1_ar, s1_y, s2, update(1, nth(1, ar2_vs) + nth(26, ar2_vs), ar2_vs), bigArray_vs, points_vs);
 {
    //@ open world(s1_x, s1_ar, s1_y, s2, ar2_vs, bigArray_vs, points_vs);
    //@ open ar2_g(ar2_vs);
    ar2[ 1] = ar2[ 1] + ar2[26];
    //@ close ar2_g(update(1, nth(1, ar2_vs) + nth(26, ar2_vs), ar2_vs));
    //@ close world(s1_x, s1_ar, s1_y, s2, update(1, nth(1, ar2_vs) + nth(26, ar2_vs), ar2_vs), bigArray_vs, points_vs);
    return;
 }


// TODO: make this function pass the verification
/*main() function
-params: an integer arguement and a character pointer argument
-description: This function does some checking on global and local structs or array. 
It makes sure to return 0.
*/
int main(int argc, char **argv) //@ : main_full(static_array_main_nl)
 {
    //@ open static_array_main_nl();
  
    struct_with_array *bigArrayPtr = bigArray;
  
    foo();

    struct_with_array *s;
    int    i = 1;
    int    ar1 [55];
    int    t;

    /* normal array */
    ar1[ 0] = 1;
    ar1[ 1] = 5;
    ar1[ 2] = 0;
    ar1[26] = 2;
    ar1[ 1] = ar1[ 1] + ar1[26];

    if (ar1[i] == 7)
    { t = ar1[2]; }
    else
    { assert(false); }
    //@ assert t == 0;

    assert (ar1[26] == 2);

    /* array inside a struct */
    s = malloc (sizeof (struct_with_array));
    if (s == 0) { abort(); }
    //@ chars_to_struct_with_array_(s);
    //@ open s->x |-> _;
    //@ open ints_(s->ar, 7, _);
    //@ open s->y |-> _;

    s->ar[ 0] = 1;
    s->ar[ 1] = 5;
    s->ar[ 2] = 0;
    s->ar[ 6] = 2;
    s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

    if (s->ar[i] == 7)
    { t += s->ar[2]; }
    else
    { assert(false); }
    //@ assert t == 0;

    assert (s->ar[0] == 1);
    //@ close s->x |-> _;
    //@ close ints_(s->ar, 7, _);
    //@ close s->y |-> _;
    //@ struct_with_array_to_chars_(s);
    free (s);


    /* global array */
    //@ open world(?s1_x, ?s1_ar, ?s1_y, ?s2, ?ar2_vs, ?bigArray_vs, ?points_vs);
    //@ open ar2_g(ar2_vs);
    ar2[ 0] = 1;
    ar2[ 1] = 5;
    ar2[ 2] = 0;
    ar2[26] = 2;
    //@ list<int> ar2_vs_before_mod = update(26, 2, update(2, 0, update(1, 5, update(0, 1, ar2_vs))));
    //@ close ar2_g(ar2_vs_before_mod);
    //@ close world(s1_x, s1_ar, s1_y, s2, ar2_vs_before_mod, bigArray_vs, points_vs);
    
    //@ assert 0 <= 5 && 5 <= 50;
    //@ assert 0 <= 2 && 2 <= 50;
    mod_ar2 ();
    //@ open world(_, _, _, _, ?ar2_vs_after_mod, _, _);
    //@ open ar2_g(ar2_vs_after_mod);

    if (ar2[i] == 7)
    { t += ar2[2]; }
    else
    { assert(false); }
    //@ assert t == 0;

    assert (ar2[1] == 7);
    //@ close ar2_g(ar2_vs_after_mod);
    //@ close world(s1_x, s1_ar, s1_y, s2, ar2_vs_after_mod, bigArray_vs, points_vs);

    //@ open world(_, _, _, _, _, _, ?points_vs_final);
    //@ open points_g(points_vs_final);
    //@ open point_arr(points, 2, points_vs_final);
    //@ open point_components(points, _, _);
    //@ open point_arr(points + 1, 1, tail(points_vs_final));
    //@ open point_components(points + 1, _, _);
    assert (points[1].y == 40);
    //@ close point_components(points + 1, 30, 40);
    //@ close point_arr(points + 1, 1, tail(points_vs_final));
    //@ close point_components(points, 10, 20);
    //@ close point_arr(points, 2, points_vs_final);
    //@ close points_g(points_vs_final);
    //@ close world(s1_x, s1_ar, s1_y, s2, ar2_vs_after_mod, bigArray_vs, points_vs_final);
  
    int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
    xs[1] = xs[2];
    assert (xs[1] == 3);
    ys[2] = ys[3];
    assert (ys[2] == 7);

    return (t);
 }