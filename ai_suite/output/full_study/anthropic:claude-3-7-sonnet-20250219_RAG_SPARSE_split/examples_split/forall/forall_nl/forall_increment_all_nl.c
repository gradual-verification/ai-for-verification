// TODO: make this function pass the verification
/***
 * Description:
The increment_all function increments all elements by 1 in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes suer that the array has its N elements incremented by 1.
*/

/*@
  requires a[0..N] |-> ?values &*& 0 <= N;
  ensures a[0..N] |-> ?new_values &*& 
          length(new_values) == length(values) &*&
          (length(values) == 0 ? new_values == nil : 
            (forall_nth(values, (le)(unit, 0)) ? 
              forall(zip(values, new_values), (add_one)(unit)) == true : 
              true));
  
  fixpoint bool add_one(unit u, pair<int, int> p) {
    switch(u) {
      case unit: return p.snd == p.fst + 1;
    }
  }
  
  fixpoint bool le(unit u, int x, int y) {
    switch(u) {
      case unit: return x <= y;
    }
  }
  
  fixpoint list<pair<t1, t2> > zip<t1, t2>(list<t1> l1, list<t2> l2) {
    switch(l1) {
      case nil: return nil;
      case cons(h1, t1): 
        return switch(l2) {
          case nil: return nil;
          case cons(h2, t2): return cons(pair(h1, h2), zip(t1, t2));
        };
    }
  }
@*/
void increment_all(int* a, int N) 
{
  int k = 0;
  /*@
    invariant a[0..k] |-> ?processed &*& a[k..N] |-> ?remaining &*& 
              0 <= k &*& k <= N &*&
              length(processed) == k &*&
              (k == 0 ? processed == nil : 
                (forall_nth(take(k, values), (le)(unit, 0)) ? 
                  forall(zip(take(k, values), processed), (add_one)(unit)) == true : 
                  true)) &*&
              remaining == drop(k, values);
  @*/
  while(k < N)
  {
    //@ open ints(a + k, _, _);
    a[k] = a[k] + 1;
    //@ close ints(a + k, 1, cons(a[k], nil));
    //@ ints_join(a);
    k++;
  }
}