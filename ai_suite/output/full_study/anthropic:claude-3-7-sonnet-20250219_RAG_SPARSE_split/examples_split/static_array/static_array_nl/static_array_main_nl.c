#include <stdlib.h>
#include <string.h>


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
//@ requires true;
//@ ensures true;
{
  struct mystruct my_local_nested_struct;
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ assert &my_global_nested_struct != &my_local_nested_struct;
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  //@ assert sh != &my_global_nested_struct;
  //@ assert sh != &my_local_nested_struct;
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  (&sh->s1)->ar[5] = 300;
  free(sh);
}



/*mod_ar2() function
-params: none
-description: This function modifies a global array. 

It requires that the first and 26-th elements are in the range of 0 ~ 50.
It ensures that the first element is updated to the sum of the first and 26-th elements.
*/
void mod_ar2 (void)
//@ requires ar2[1] |-> ?v1 &*& ar2[26] |-> ?v2 &*& 0 <= v1 &*& v1 <= 50 &*& 0 <= v2 &*& v2 <= 50;
//@ ensures ar2[1] |-> (v1 + v2) &*& ar2[26] |-> v2;
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }


/*main() function
-params: an integer arguement and a character pointer argument
-description: This function does some checking on global and local structs or array. 
It makes sure to return 0.
*/
int main(int argc, char **argv) //@ : main_full(static_array_main_nl)
//@ requires module(static_array_main_nl, true) &*& 0 <= argc &*& [_]argv(argv, argc, ?arguments);
//@ ensures true;
 {
  
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

  //@ assert ar1[1] |-> 7;
  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  //@ assert ar1[26] |-> 2;

  /* array inside a struct */
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }

  s->ar[ 0] = 1;
  s->ar[ 1] = 5;
  s->ar[ 2] = 0;
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

  //@ assert s->ar[1] |-> 7;
  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }

  //@ assert s->ar[0] |-> 1;
  free (s);


  /* global array */
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  mod_ar2 ();

  //@ assert ar2[1] |-> 7;
  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  //@ assert ar2[1] |-> 7;

  //@ assert points[1].y |-> 40;
  
  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  //@ assert xs[1] |-> 3;
  ys[2] = ys[3];
  //@ assert ys[2] |-> 7;

  return (t);
 }