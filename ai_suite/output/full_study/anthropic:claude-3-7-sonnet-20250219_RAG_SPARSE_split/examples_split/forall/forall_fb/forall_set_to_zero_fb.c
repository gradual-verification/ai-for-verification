// TODO: make this function pass the verification
void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  //@ length_nonnegative(vs);
  
  while(k < N) 
    //@ invariant 0 <= k &*& k <= N &*& a[0..k] |-> ?prefix &*& a[k..N] |-> ?suffix &*& forall_(int i; i < 0 || i >= k || nth(i, prefix) == 0);
  {
    a[k] = 0;
    //@ assert a[k] |-> 0;
    //@ assert a[k+1..N] |-> ?new_suffix;
    //@ assert a[0..k] |-> ?old_prefix;
    //@ close a[0..k+1] |-> append(old_prefix, cons(0, nil));
    //@ assert a[0..k+1] |-> ?new_prefix;
    
    //@ assert forall_(int i; i < 0 || i >= k || nth(i, old_prefix) == 0);
    //@ assert nth(k, new_prefix) == 0;
    
    /*@
    {
      produce_lemma_function_pointer_chunk forall_nth_update() {
        forall_elim(int i; i < 0 || i >= k || nth(i, old_prefix) == 0, k);
        assert i < 0 || i >= k || nth(i, old_prefix) == 0;
      }
    }
    @*/
    
    /*@
    {
      produce_lemma_function_pointer_chunk forall_nth_append() {
        forall_intro(int i; i < 0 || i >= k+1 || nth(i, new_prefix) == 0);
        if (0 <= i && i < k+1) {
          if (i == k) {
            nth_append_r(old_prefix, cons(0, nil), 0);
            assert nth(i, new_prefix) == 0;
          } else {
            nth_append(old_prefix, cons(0, nil), i);
            forall_elim(int j; j < 0 || j >= k || nth(j, old_prefix) == 0, i);
            assert nth(i, new_prefix) == 0;
          }
        }
      }
    }
    @*/
    
    k++;
  }
  
  /*@
  {
    produce_lemma_function_pointer_chunk forall_nth_final() {
      forall_intro(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
      if (0 <= i && i < length(vs)) {
        assert i < N;
        forall_elim(int j; j < 0 || j >= N || nth(j, prefix) == 0, i);
        assert nth(i, nvs) == 0;
      }
    }
  }
  @*/
}