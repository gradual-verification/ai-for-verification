#include <stdlib.h>
#include <string.h>


typedef struct
 {
  int x;
  int ar [7];
  int y;
 } struct_with_array;

//@ predicate struct_with_array(struct_with_array *s;) = s->x |-> _ &*& ints(s->ar, 7, _) &*& s->y |-> _;

struct mystruct {
  struct_with_array s1;
  int s2;
};

//@ predicate mystruct(struct mystruct *s;) = struct_with_array(&s->s1) &*& s->s2 |-> _;

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static int ar2 [55];

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; // Incomplete initializer lists; remaining elements get default value.

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };


// TODO: make this function pass the verification
/*mod_ar2() function
-params: none
-description: This function modifies a global array. 

It requires that the first and 26-th elements are in the range of 0 ~ 50.
It ensures that the first element is updated to the sum of the first and 26-th elements.
*/
void mod_ar2 (void)
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }


