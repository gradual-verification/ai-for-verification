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
  //@ invariant lo <= j &*& j <= hi &*& lo - 1 <= i &*& i < j &*& a[lo..i+1] |-> ?vs_low &*& a[i+1..j] |-> ?vs_high &*& a[j..hi] |-> ?vs_rest &*& a[hi] |-> pivot &*& forall(vs_low, (ge)(pivot)) == true &*& forall(vs_high, (le)(pivot)) == true &*& append(append(vs_low, vs_high), append(vs_rest, cons(pivot, nil))) == vs;
  {
   
    int aj = a[j];
    if (aj < pivot) {
      i++;
      if (i < j) {
        //@ assert a[i] |-> ?vi;
        //@ assert a[j] |-> aj;
        swap(a, i, j);
        //@ assert a[i] |-> aj;
        //@ assert a[j] |-> vi;
        //@ assert vs_high == cons(vi, ?vs_high_rest);
        //@ assert vs_low == ?vs_low_old;
        //@ assert forall(vs_low_old, (ge)(pivot)) == true;
        //@ assert forall(vs_high_rest, (le)(pivot)) == true;
        //@ assert aj < pivot;
        //@ assert vi >= pivot;
        //@ assert a[lo..i] |-> vs_low_old;
        //@ assert a[i] |-> aj;
        //@ assert a[i+1..j] |-> vs_high_rest;
        //@ assert a[j] |-> vi;
        //@ assert a[j+1..hi] |-> vs_rest;
        //@ assert a[hi] |-> pivot;
        //@ assert forall(vs_low_old, (ge)(pivot)) == true;
        //@ assert forall(cons(aj, nil), (ge)(pivot)) == false;
        //@ assert forall(vs_high_rest, (le)(pivot)) == true;
        //@ assert forall(cons(vi, nil), (le)(pivot)) == true;
      } else {
        //@ assert i == j-1;
        //@ assert vs_high == nil;
        //@ assert a[lo..i+1] |-> vs_low;
        //@ assert a[i+1..j] |-> vs_high;
        //@ assert a[j..hi] |-> vs_rest;
        //@ assert a[hi] |-> pivot;
      }
    } else {
      //@ assert aj >= pivot;
      //@ assert a[lo..i+1] |-> vs_low;
      //@ assert a[i+1..j] |-> vs_high;
      //@ assert a[j] |-> aj;
      //@ assert a[j+1..hi] |-> vs_rest;
      //@ assert a[hi] |-> pivot;
      //@ assert forall(vs_low, (ge)(pivot)) == true;
      //@ assert forall(vs_high, (le)(pivot)) == true;
      //@ assert forall(cons(aj, nil), (le)(pivot)) == false;
    }
  }

  i++;

  if (i < hi) {
    //@ assert a[i] |-> ?ai;
    //@ assert a[hi] |-> pivot;
    swap(a, i, hi);
    //@ assert a[i] |-> pivot;
    //@ assert a[hi] |-> ai;
  } else {
    //@ assert i == hi;
  }
  return i;
}