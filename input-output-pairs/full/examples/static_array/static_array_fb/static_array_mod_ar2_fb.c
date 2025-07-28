#include <stdlib.h>
#include <string.h>


typedef struct
 {
  int x;
  int ar [7];
  int y;

// TODO: make this function pass the verification
void mod_ar2 (void)
/*@ requires ar2[0..55] |-> ?elems
    &*& nth (1, elems) >= 0 &*& nth (1, elems) <= 50
    &*& nth (26, elems) >= 0 &*& nth (26, elems) <= 50;
  @*/
/*@ ensures ar2[0..55] |-> update (1, nth (1, elems) + nth (26, elems), elems);
  @*/
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }

