#include <stdlib.h>
#include <string.h>


typedef struct
 {
  int x;
  int ar [7];
  int y;

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


