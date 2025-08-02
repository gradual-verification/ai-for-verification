// TODO: make this function pass the verification
/***
 * Description:
The set_to_zero function sets 0 to the elements in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes sure that the array has its N elements to be 0. 
*/
void set_to_zero(int* a, int N) 
//@ requires a[0..N] |-> ?vs &*& N >= 0;
//@ ensures a[0..N] |-> ?vs2 &*& forall(vs2, (eq)(0)) == true;
{
  int k = 0;
  //@ close ints(a, 0, nil);
  while(k < N) 
  //@ invariant a[0..k] |-> ?vs1 &*& a[k..N] |-> ?vs2 &*& forall(vs1, (eq)(0)) == true;
  {
    a[k] = 0;
    k++;
    //@ close ints(a, k, ?vs3);
  }
}