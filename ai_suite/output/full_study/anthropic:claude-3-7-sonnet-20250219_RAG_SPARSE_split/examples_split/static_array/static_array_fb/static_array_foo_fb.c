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
static void foo()
  //@ requires mystruct(&my_global_nested_struct);
  //@ ensures mystruct(&my_global_nested_struct);
{
  struct mystruct my_local_nested_struct;
  
  //@ open mystruct(&my_global_nested_struct);
  //@ open struct_with_array(&my_global_nested_struct.s1);
  
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ close_struct_zero(&my_local_nested_struct);
  //@ close struct_with_array(&my_local_nested_struct.s1);
  //@ close mystruct(&my_local_nested_struct);
  
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ open mystruct(&my_local_nested_struct);
  //@ close_struct_zero(&my_local_nested_struct.s1);
  //@ close struct_with_array(&my_local_nested_struct.s1);
  //@ close mystruct(&my_local_nested_struct);
  
  assert(&my_global_nested_struct != &my_local_nested_struct);
  
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  
  //@ close_struct_zero(sh);
  //@ close struct_with_array(&sh->s1);
  //@ close mystruct(sh);
  
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  
  //@ open mystruct(&my_global_nested_struct);
  //@ open struct_with_array(&my_global_nested_struct.s1);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  //@ close struct_with_array(&my_global_nested_struct.s1);
  //@ close mystruct(&my_global_nested_struct);
  
  //@ open mystruct(&my_local_nested_struct);
  //@ open struct_with_array(&my_local_nested_struct.s1);
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ close struct_with_array(&my_local_nested_struct.s1);
  //@ close mystruct(&my_local_nested_struct);
  
  //@ open mystruct(sh);
  //@ open struct_with_array(&sh->s1);
  (&sh->s1)->ar[5] = 300;
  //@ close struct_with_array(&sh->s1);
  //@ close mystruct(sh);
  
  //@ open mystruct(sh);
  //@ open struct_with_array(&sh->s1);
  free(sh);
}