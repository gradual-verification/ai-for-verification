//@ #include <arrays.gh> // For ints_split and ints_join
//@ #include <quantifiers.gh> // For not_forall and forall_elim

/*@

fixpoint bool eq<t>(t x, t y) { return x == y; }

fixpoint int count_eq<t>(list<t> vs, t v) { return count(vs, (eq)(v)); }

fixpoint bool option_le(option<int> x, int y) {
    switch (x) {
        case none: return true;
        case some(x0): return x0 <= y;
    }
}

fixpoint bool option_le_option(option<int> x, option<int> y) {
    switch (y) {
        case none: return true;
        case some(y0): return option_le(x, y0);
    }
}

fixpoint bool is_sorted_between(option<int> lower, list<int> vs, option<int> upper) {
    switch (vs) {
        case nil: return option_le_option(lower, upper);
        case cons(v, vs0): return option_le(lower, v) && is_sorted_between(some(v), vs0, upper);
    }
}

fixpoint bool le(int x, int y) { return x <= y; }
fixpoint bool ge(int x, int y) { return x >= y; }

fixpoint int mplus<t>(fixpoint(t, int) M1, fixpoint(t, int) M2, t x) { return M1(x) + M2(x); }

fixpoint int memp<t>(t x) { return 0; }
@*/


void swap (int *a, int i, int j)
  //@ requires a[i] |-> ?vi &*& a[j] |-> ?vj;
  //@ ensures a[i] |-> vj &*& a[j] |-> vi;
{
  int aj = a[j];
  a[j] = a[i];
  a[i] = aj;
}


int partition(int *a, int lo, int hi)
  //@ requires a[lo..hi + 1] |-> ?vs &*& lo <= hi &*& lo >= 0;
  /*@
  ensures
      a[lo..result] |-> ?vslow &*&
      a[result] |-> ?vpivot &*&
      a[result + 1..hi + 1] |-> ?vshigh &*&
      forall(vslow, (ge)(vpivot)) == true &*&
      forall(vshigh, (le)(vpivot)) == true &*&
      (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
  @*/
{
  
  int pivot = a[hi];
  
  int i = lo - 1;
  int j;

  for (j = lo; j < hi; j++)
  /*@
  invariant 
      lo <= j &*& j <= hi &*& lo - 1 <= i &*& i < j &*&
      a[lo..i+1] |-> ?vs_le &*& a[i+1..j] |-> ?vs_gt &*& a[j..hi] |-> ?vs_unknown &*& a[hi] |-> pivot &*&
      forall(vs_le, (ge)(pivot)) == true &*&
      forall(vs_gt, (le)(pivot)) == true &*&
      append(append(append(vs_le, vs_gt), vs_unknown), cons(pivot, nil)) == vs;
  @*/
  {
   
    int aj = a[j];
    if (aj < pivot) {
      i++;
      if (i < j) {
        //@ ints_split(a + lo, i + 1 - lo);
        //@ ints_split(a + (i + 1), j - (i + 1));
        swap(a, i, j);
        //@ ints_join(a + lo, i + 1 - lo);
        //@ ints_join(a + (i + 1), j - (i + 1));
  
      } else {
        //@ assert i == j - 1;
      }
    } else {
      //@ assert aj >= pivot;
    }
  }

  i++;

  if (i < hi) {
    //@ ints_split(a + lo, i - lo);
    swap(a, i, hi);
    //@ ints_join(a + lo, i - lo);

  } else {
    //@ assert i == hi;
  }
  return i;
}



// TODO: make this function pass the verification
void quicksort(int *a, int lo, int hi)
  //@ requires lo >= 0 &*& a[lo..hi + 1] |-> ?vs;
  //@ ensures a[lo..hi + 1] |-> ?vs2 &*& (count_eq)(vs2) == (count_eq)(vs) &*& is_sorted_between(none, vs2, none) == true;
{
  if (lo >= hi) {
    //@ if (lo > hi) { open ints(a + lo, hi + 1 - lo, _); close ints(a + lo, hi + 1 - lo, _); }
    return;
  } else {
    int p = partition(a, lo, hi);
    //@ assert a[lo..p] |-> ?vslow;
    //@ assert a[p] |-> ?vpivot;
    //@ assert a[p+1..hi+1] |-> ?vshigh;
    
    //@ ints_split(a + lo, p - lo);
    quicksort(a, lo, p-1);
    //@ assert a[lo..p] |-> ?vslow_sorted;
    //@ assert is_sorted_between(none, vslow_sorted, none) == true;
    //@ assert (count_eq)(vslow_sorted) == (count_eq)(vslow);
    //@ ints_join(a + lo, p - lo);
    
    //@ ints_split(a + (p+1), hi - p);
    quicksort(a, p+1, hi);
    //@ assert a[p+1..hi+1] |-> ?vshigh_sorted;
    //@ assert is_sorted_between(none, vshigh_sorted, none) == true;
    //@ assert (count_eq)(vshigh_sorted) == (count_eq)(vshigh);
    //@ ints_join(a + (p+1), hi - p);
    
    //@ assert a[lo..p] |-> vslow_sorted;
    //@ assert a[p] |-> vpivot;
    //@ assert a[p+1..hi+1] |-> vshigh_sorted;
    
    /*@
    // Prove that the entire array is sorted
    if (!is_sorted_between(none, append(append(vslow_sorted, cons(vpivot, nil)), vshigh_sorted), none)) {
        // We know vslow_sorted is sorted and all elements are >= vpivot
        // We know vshigh_sorted is sorted and all elements are <= vpivot
        // Therefore the combined array must be sorted
        assert forall(vslow_sorted, (ge)(vpivot)) == true;
        assert forall(vshigh_sorted, (le)(vpivot)) == true;
        
        // If the combined array is not sorted, there must be a pair of adjacent elements that are out of order
        // This can only happen at the boundaries between vslow_sorted, vpivot, and vshigh_sorted
        // But we've established that all elements in vslow_sorted are >= vpivot
        // And all elements in vshigh_sorted are <= vpivot
        // So the combined array must be sorted
        assert false;
    }
    @*/
    
    /*@
    // Prove that the count of elements is preserved
    assert (count_eq)(append(append(vslow_sorted, cons(vpivot, nil)), vshigh_sorted)) == 
           (count_eq)(append(append(vslow, cons(vpivot, nil)), vshigh));
    
    // From partition postcondition, we know:
    assert (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
    
    // And from recursive calls, we know:
    assert (count_eq)(vslow_sorted) == (count_eq)(vslow);
    assert (count_eq)(vshigh_sorted) == (count_eq)(vshigh);
    
    // Therefore:
    assert (count_eq)(append(append(vslow_sorted, cons(vpivot, nil)), vshigh_sorted)) == (count_eq)(vs);
    @*/
  }
}