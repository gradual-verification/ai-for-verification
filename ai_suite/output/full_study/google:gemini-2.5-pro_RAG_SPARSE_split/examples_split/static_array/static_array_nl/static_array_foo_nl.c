#include <stdlib.h>
#include <string.h>
#include <assert.h>

//@ #include <list.gh>


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

/*@

predicate struct_with_array_p(struct_with_array *s; int x, list<int> ar, int y) =
    s->x |-> x &*&
    ints(s->ar, 7, ar) &*&
    s->y |-> y;

predicate mystruct_p(struct mystruct *s; int s1_x, list<int> s1_ar, int s1_y, int s2) =
    struct_with_array_p(&s->s1, s1_x, s1_ar, s1_y) &*&
    s->s2 |-> s2;

@*/

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
// TODO: make this function pass the verification
static void foo()
    //@ requires mystruct_p(&my_global_nested_struct, ?x, ?ar, ?y, ?s2);
    //@ ensures mystruct_p(&my_global_nested_struct, x, update(5, 100, ar), y, s2);
{
  struct mystruct my_local_nested_struct;
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  
  //@ open mystruct_p(&my_global_nested_struct, x, ar, y, s2);
  //@ open struct_with_array_p(&my_global_nested_struct.s1, x, ar, y);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close struct_with_array_p(&my_global_nested_struct.s1, x, update(5, 100, ar), y);
  //@ close mystruct_p(&my_global_nested_struct, x, update(5, 100, ar), y, s2);
  
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  
  //@ open_struct(sh);
  (&sh->s1)->ar[5] = 300;
  //@ close_struct(sh);
  
  free(sh);
}
