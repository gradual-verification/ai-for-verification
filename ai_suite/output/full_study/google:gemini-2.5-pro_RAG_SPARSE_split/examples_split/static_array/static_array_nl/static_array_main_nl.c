#include <stdlib.h>
#include <string.h>
#include <assert.h>
//@ #include "listex.gh"
//@ #include <stddef.h>

/*@

// Predicate for struct_with_array
predicate struct_with_array_p(struct_with_array *s; int x, list<int> ar_vals, int y) =
    s->x |-> x &*&
    ints(s->ar, 7, ar_vals) &*&
    s->y |-> y;

// Predicate for mystruct
predicate mystruct_p(struct mystruct *s; int x, list<int> ar_vals, int y, int s2) =
    s->s1.x |-> x &*&
    ints(s->s1.ar, 7, ar_vals) &*&
    s->s1.y |-> y &*&
    s->s2 |-> s2;

// Predicate for the global mystruct instance
predicate my_global_nested_struct_p(int x, list<int> ar_vals, int y, int s2) =
    mystruct_p(&my_global_nested_struct, x, ar_vals, y, s2);

// Predicate for the global array ar2
predicate ar2_p(list<int> vals) =
    ints(ar2, 55, vals);

// Predicate for an array of struct_with_array
predicate struct_with_array_array_p(struct_with_array *arr, int count; list<pair<int, pair<list<int>, int> > > values) =
    count == 0 ?
        values == nil
    :
        struct_with_array_p(arr, ?x, ?ar_vals, ?y) &*&
        struct_with_array_array_p(arr + 1, count - 1, ?tail_values) &*&
        values == cons(pair(x, pair(ar_vals, y)), tail_values);

// Predicate for the global bigArray
predicate bigArray_p(list<pair<int, pair<list<int>, int> > > values) =
    struct_with_array_array_p(bigArray, 10, values);

// Predicate for struct point
predicate point_p(struct point *p; int x, int y) =
    p->x |-> x &*& p->y |-> y;

// Predicate for an array of struct point
predicate point_array_p(struct point *arr, int count; list<pair<int, int> > values) =
    count == 0 ?
        values == nil
    :
        point_p(arr, ?x, ?y) &*&
        point_array_p(arr + 1, count - 1, ?tail_values) &*&
        values == cons(pair(x, y), tail_values);

// Predicate for the global points array
predicate points_p(list<pair<int, int> > values) =
    point_array_p(points, 2, values);

// Predicate for the initial state of all globals
predicate globals() =
    my_global_nested_struct_p(42, {420, 421, 422, 423, 424, 425, 426}, -3, -99) &*&
    ar2_p(repeat(0, 55)) &*&
    bigArray_p(
        cons(pair(100, pair({1,2,3,4,0,0,0}, 200)),
        cons(pair(300, pair({5,6,7,0,0,0,0}, 400)),
        repeat(pair(0, pair(repeat(0, 7), 0)), 8)))
    ) &*&
    points_p({pair(10, 20), pair(30, 40)});

// Module definition for main
module_code(static_array_main_nl)
{
    requires true;
    ensures globals();
}

// Auto-generated lemma stubs for converting between structs and chars
lemma void chars_to_mystruct_p(struct mystruct *s);
    requires chars(s, sizeof(struct mystruct), _);
    ensures mystruct_p(s, _, _, _, _);

lemma void chars_to_struct_with_array_p(struct_with_array *s);
    requires chars(s, sizeof(struct_with_array), _);
    ensures struct_with_array_p(s, _, _, _);

@*/

typedef struct
 {
  int x;
  int ar [7];
  int y;

 } struct_with_array;


struct mystruct {
  struct_with_array s1;
  int s2;
};


struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static int ar2 [55];

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; // Incomplete initializer lists; remaining elements get default value.

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };


/*foo() function
-params: none
-description: This function checks if the global struct is different from the local structs.
It makes sure that my_global_nested_struct still keeps the structure of mystruct. 
*/
static void foo()
//@ requires my_global_nested_struct_p(?x, ?ar_vals, ?y, ?s2) &*& length(ar_vals) == 7;
//@ ensures my_global_nested_struct_p(x, update(5, 100, ar_vals), y, s2);
{
  struct mystruct my_local_nested_struct;
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  
  //@ chars_split(&my_local_nested_struct, sizeof(struct_with_array));
  //@ chars_to_chars_(&my_local_nested_struct);
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ chars_join(&my_local_nested_struct);
  
  //@ chars_to_mystruct_p(&my_local_nested_struct);
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ chars_to_mystruct_p(sh);
  
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  
  //@ open my_global_nested_struct_p(x, ar_vals, y, s2);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close my_global_nested_struct_p(x, update(5, 100, ar_vals), y, s2);
  
  //@ open mystruct_p(&my_local_nested_struct, ?llx, ?llar, ?lly, ?lls2);
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ close mystruct_p(&my_local_nested_struct, llx, update(5, 200, llar), lly, lls2);
  
  //@ open mystruct_p(sh, ?shx, ?shar, ?shy, ?shs2);
  (&sh->s1)->ar[5] = 300;
  //@ close mystruct_p(sh, shx, update(5, 300, shar), shy, shs2);
  
  free(sh);
  //@ open mystruct_p(sh, _, _, _, _);
  //@ open struct_with_array_p(&sh->s1, _, _, _);
  //@ open ints(sh->s1.ar, 7, _);
}



/*mod_ar2() function
-params: none
-description: This function modifies a global array. 

It requires that the first and 26-th elements are in the range of 0 ~ 50.
It ensures that the first element is updated to the sum of the first and 26-th elements.
*/
void mod_ar2 (void)
//@ requires ar2_p(?vals) &*& length(vals) == 55 &*& 0 <= nth(1, vals) &*& nth(1, vals) <= 50 &*& 0 <= nth(26, vals) &*& nth(26, vals) <= 50;
//@ ensures ar2_p(update(1, nth(1, vals) + nth(26, vals), vals));
 {
  //@ open ar2_p(vals);
  ar2[ 1] = ar2[ 1] + ar2[26];
  //@ close ar2_p(update(1, nth(1, vals) + nth(26, vals), vals));
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
  //@ open module(static_array_main_nl, true);
  
  struct_with_array *bigArrayPtr = bigArray;
  
  foo();

  struct_with_array *s;
  int    i = 1;
  int    ar1 [55];
  int    t = 0;

  /* normal array */
  ar1[ 0] = 1;
  ar1[ 1] = 5;
  ar1[ 2] = 0;
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);

  /* array inside a struct */
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }
  //@ chars_to_struct_with_array_p(s);
  //@ open struct_with_array_p(s, ?sx, ?sar, ?sy);

  s->ar[ 0] = 1;
  s->ar[ 1] = 5;
  s->ar[ 2] = 0;
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }

  assert (s->ar[0] == 1);
  //@ list<int> sar_final = update(1, 7, update(6, 2, update(2, 0, update(1, 5, update(0, 1, sar)))));
  //@ close struct_with_array_p(s, sx, sar_final, sy);
  free (s);
  //@ open struct_with_array_p(s, _, _, _);
  //@ open ints(s->ar, 7, _);


  /* global array */
  //@ open ar2_p(?ar2_vals_before);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  //@ list<int> ar2_vals_after_assigns = update(26, 2, update(2, 0, update(1, 5, update(0, 1, ar2_vals_before))));
  //@ close ar2_p(ar2_vals_after_assigns);
  
  mod_ar2 ();
  //@ assert ar2_p(update(1, 7, ar2_vals_after_assigns));

  //@ open ar2_p(?ar2_vals_after_mod);
  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  assert (ar2[1] == 7);
  //@ close ar2_p(ar2_vals_after_mod);

  //@ open points_p(?points_vals);
  assert (points[1].y == 40);
  //@ close points_p(points_vals);
  
  int xs[] = {1, 2, 3};
  int ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);

  return (t);
 }