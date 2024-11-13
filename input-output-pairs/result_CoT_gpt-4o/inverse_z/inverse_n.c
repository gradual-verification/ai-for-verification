//@ #include "nat.gh"
//@ #include "listex.gh"

/*@
predicate permutation(int* A, int N) =
  array_segment(A, N, ?lst) &*&
  true == mem_ints(0, lst) &*&
  true == mem_ints(N-1, lst) &*&
  true == all_eq(true, map(is_perm(lst, N), lst)); 

predicate array(int* arr, int N) = 
  array_segment(arr, N, _);

@*/


/*@
requires array(A, N) &*& array(B, N) &*& permutation(A, N) &*& 0 <= N;
ensures array(A, N) &*& array(B, N) &*& permutation_inverse(A, B, N);
@*/
void invert(int *A, int N, int *B)
{
  /*@
  loop invariant 0 <= i <= N &*& array(A, N) &*& array(B, N) &*& permutation(A, N);
  @*/
  for (int i = 0; i < N; i++)
  {
    //@ open permutation(A, N);
    int ai = A[i];
    //@ close permutation(A, N);
    //@ open array(B, N);
    B[ai] = i;
    //@ close array(B, N);
  }  
}

int main()
{
    return 0;
}
