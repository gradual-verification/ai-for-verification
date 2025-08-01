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

  {
   
    int aj = a[j];
    if (aj < pivot) {
      i++;
      if (i < j) {
        swap(a, i, j);
  
      } else {
  
      }
    } else {
  
    }
  }

  i++;

  if (i < hi) {
    swap(a, i, hi);

  } else {

  }
  return i;
}



// TODO: make this function pass the verification
void quicksort(int *a, int lo, int hi)
  //@ requires lo >= 0 &*& hi < INT_MAX &*& a[lo..hi + 1] |-> ?vs;
  //@ ensures a[lo..hi + 1] |-> ?vs2 &*& (count_eq)(vs2) == (count_eq)(vs) &*& is_sorted_between(none, vs2, none) == true;
{
  if (lo > hi) {

    return;
  } else {
    int p = partition(a, lo, hi);

    quicksort(a, lo, p-1);
    quicksort(a, p+1, hi);

  }
}

