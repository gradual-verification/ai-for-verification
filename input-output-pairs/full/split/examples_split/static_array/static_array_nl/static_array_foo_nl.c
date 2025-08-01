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