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

lemma_auto void mplus_comm(fixpoint(int, int) f1, fixpoint(int, int) f2)
    requires true;
    ensures mplus(f1, f2) == mplus(f2, f1);
{
    int x = not_forall_t(get_forall_t<int>(), (eq_int_fun)(mplus(f1, f2), mplus(f2, f1)));
    assert f1(x) + f2(x) == f2(x) + f1(x);
    assert false;
}

lemma_auto void mplus_assoc(fixpoint(int, int) f1, fixpoint(int, int) f2, fixpoint(int, int) f3)
    requires true;
    ensures mplus(mplus(f1, f2), f3) == mplus(f1, mplus(f2, f3));
{
    int x = not_forall_t(get_forall_t<int>(), (eq_int_fun)(mplus(mplus(f1, f2), f3), mplus(f1, mplus(f2, f3))));
    assert (f1(x) + f2(x)) + f3(x) == f1(x) + (f2(x) + f3(x));
    assert false;
}

lemma_auto void count_eq_append<t>(list<t> l1, list<t> l2)
    requires true;
    ensures (count_eq)(append(l1, l2)) == mplus((count_eq)(l1), (count_eq)(l2));
{
    switch(l1) {
        case nil:
            assert (count_eq)(nil) == memp;
        case cons(h, t):
            count_eq_append(t, l2);
            int x = not_forall_t(get_forall_t<int>(), (eq_int_fun)((count_eq)(append(cons(h,t), l2)), mplus((count_eq)(cons(h,t)), (count_eq)(l2))));
            count_append(cons(h,t), l2, (eq)(x));
            count_append(t, l2, (eq)(x));
            assert false;
    }
}

@*/


void swap (int *a, int i, int j)
  //@ requires a[i] |-> ?vi &*& a[j] |-> ?vj;
  //@ ensures a[i] |-> vj &*& a[j] |-> vi;
{
  int aj = a[j];
  a[j] = a[i];
  a[i] = aj;
}


// TODO: make this function pass the verification
int partition(int *a, int lo, int hi)
  //@ requires a[lo..hi + 1] |-> ?vs &*& lo <= hi &*& lo >= 0;
  /*@
  ensures
      a[lo..result] |-> ?vslow &*&
      a[result] |-> ?vpivot &*&
      a[result + 1..hi + 1] |-> ?vshigh &*&
      forall(vslow, (le)(vpivot)) == true &*&
      forall(vshigh, (ge)(vpivot)) == true &*&
      (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
  @*/
{
  //@ ints_split(a, hi);
  //@ ints_split(a, lo);
  //@ assert a[lo..hi] |-> ?vs_body &*& a[hi] |-> ?pivot_val;
  int pivot = a[hi];
  //@ assert vs == append(vs_body, cons(pivot, nil));
  
  int i = lo - 1;
  int j;

  for (j = lo; j < hi; j++)
    /*@
    invariant
        lo <= j &*& j <= hi &*&
        lo - 1 <= i &*& i < j &*&
        a[lo..i + 1] |-> ?vsl &*&
        a[i + 1..j] |-> ?vsg &*&
        a[j..hi + 1] |-> ?vsu &*&
        last(vsu) == pivot &*&
        forall(vsl, (le)(pivot)) == true &*&
        forall(vsg, (ge)(pivot)) == true &*&
        (mplus)((mplus)((count_eq)(vsl), (count_eq)(vsg))), (count_eq)(vsu)) == (count_eq)(vs);
    @*/
  {
    //@ ints_split(a, j + 1);
    //@ assert a[j] |-> ?aj_val;
    int aj = a[j];
    //@ assert head(vsu) == aj;
    
    if (aj < pivot) {
      i++;
      if (i < j) {
        //@ ints_split(a, i + 1);
        //@ assert a[i] |-> ?ai_val;
        //@ list<int> vsg_tail = tail(vsg);
        //@ forall_elim(vsg, (ge)(pivot), ai_val);
        swap(a, i, j);
        //@ forall_append(vsl, cons(aj, nil), (le)(pivot));
        //@ forall_append(vsg_tail, cons(ai_val, nil), (ge)(pivot));
        //@ list<int> vsl_new = append(vsl, cons(aj, nil));
        //@ list<int> vsg_new = append(vsg_tail, cons(ai_val, nil));
        //@ list<int> vsu_new = tail(vsu);
        //@ assert (mplus)((mplus)((count_eq)(vsl_new), (count_eq)(vsg_new))), (count_eq)(vsu_new)) == (mplus)((mplus)((count_eq)(vsl), (count_eq)(vsg))), (count_eq)(vsu));
        //@ ints_join(a);
        //@ ints_join(a);
      } else { // i == j
        //@ assert i + 1 == j;
        //@ assert vsg == nil;
        //@ forall_append(vsl, cons(aj, nil), (le)(pivot));
        //@ assert (mplus)((mplus)((count_eq)(append(vsl, cons(aj, nil))), (count_eq)(nil))), (count_eq)(tail(vsu))) == (mplus)((mplus)((count_eq)(vsl), (count_eq)(nil))), (count_eq)(vsu));
      }
    } else { // aj >= pivot
      //@ forall_append(vsg, cons(aj, nil), (ge)(pivot));
      //@ assert (mplus)((mplus)((count_eq)(vsl), (count_eq)(append(vsg, cons(aj, nil))))), (count_eq)(tail(vsu))) == (mplus)((mplus)((count_eq)(vsl), (count_eq)(vsg))), (count_eq)(vsu));
    }
    //@ ints_join(a);
  }

  //@ assert j == hi;
  //@ assert a[lo..i + 1] |-> ?vsl_final;
  //@ assert a[i + 1..hi] |-> ?vsg_final;
  //@ assert a[hi] |-> pivot;
  //@ assert vsu == cons(pivot, nil);
  
  i++;

  if (i < hi) {
    //@ ints_split(a, i + 1);
    //@ assert a[i] |-> ?pivot_candidate;
    //@ list<int> vsg_tail = tail(vsg_final);
    //@ forall_elim(vsg_final, (ge)(pivot), pivot_candidate);
    swap(a, i, hi);
    //@ forall_append(vsg_tail, cons(pivot_candidate, nil), (ge)(pivot));
    //@ ints_join(a);
    //@ list<int> vslow = vsl_final;
    //@ int vpivot = pivot;
    //@ list<int> vshigh = append(vsg_tail, cons(pivot_candidate, nil));
    //@ assert (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (mplus)((mplus)((count_eq)(vsl_final), (count_eq)(vsg_final))), (count_eq)(cons(pivot, nil)));
  } else { // i == hi
    //@ assert vsg_final == nil;
    //@ list<int> vslow = vsl_final;
    //@ int vpivot = pivot;
    //@ list<int> vshigh = nil;
    //@ assert (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (mplus)((mplus)((count_eq)(vsl_final), (count_eq)(nil))), (count_eq)(cons(pivot, nil)));
  }
  return i;
}