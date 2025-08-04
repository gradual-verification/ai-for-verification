#include "prelude.h"

/*@
// A fixpoint to generate a list of 'n' elements, all with value 'x'.
fixpoint list<int> repeat(int x, int n) {
  return n <= 0 ? nil : cons(x, repeat(x, n - 1));
}

// A lemma to prove that appending a single element 'x' to a list of 'n' 'x's
// results in a list of 'n + 1' 'x's.
lemma void repeat_append_one(int x, int n)
  requires 0 <= n;
  ensures append(repeat(x, n), cons(x, nil)) == repeat(x, n + 1);
{
  if (n > 0) {
    repeat_append_one(x, n - 1);
  }
}

// A lemma to join two adjacent 'ints' chunks. This pattern is common for
// array predicates in VeriFast.
lemma void ints_join(int *array)
    requires [?f]ints(array, ?n, ?vs) &*& [f]ints(array + n, ?n0, ?vs0);
    ensures [f]ints(array, n + n0, append(vs, vs0));
{
    open ints(array, n, vs);
    if (n > 0) {
        ints_join(array + 1);
    }
}
@*/

/***
 * Description:
The set_to_zero function sets 0 to the elements in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes sure that the array has its N elements to be 0. 
*/
void set_to_zero(int* a, int N)
  //@ requires ints(a, N, _) &*& 0 <= N;
  //@ ensures ints(a, N, repeat(0, N));
{
  int k = 0;
  while(k < N)
    /*@
    invariant
        ints(a, k, repeat(0, k)) &*&
        ints(a + k, N - k, _) &*&
        0 <= k &*& k <= N;
    @*/
  {
    // Open the chunk for the unprocessed part of the array to access a[k].
    //@ open ints(a + k, N - k, _);
    
    // Set the current element to 0.
    a[k] = 0;
    
    // Close the chunk for the single element we just modified.
    //@ close ints(a + k, 1, cons(0, nil));
    
    // Join the processed part with the newly zeroed element.
    //@ ints_join(a);
    
    // Prove that the list of values for the processed part is correct.
    //@ repeat_append_one(0, k);
    
    k++;
  }
}