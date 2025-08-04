//@ #include <arrays.gh> // For ints_split and ints_join
//@ #include <quantifiers.gh> // For not_forall and forall_elim
//@ #include <listex.gh>

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
fixpoint bool lt(int x, int y) { return x < y; }

fixpoint int mplus<t>(fixpoint(t, int) M1, fixpoint(t, int) M2, t x) { return M1(x) + M2(x); }

fixpoint int memp<t>(t x) { return 0; }

lemma void count_eq_append<t>(list<t> l1, list<t> l2, t x)
    requires true;
    ensures count_eq(append(l1, l2), x) == count_eq(l1, x) + count_eq(l2, x);
{
    count_append(l1, l2, (eq)(x));
}

lemma void mplus_comm<t>(fixpoint(t, int) f1, fixpoint(t, int) f2, t x)
    requires true;
    ensures mplus(f1, f2)(x) == mplus(f2, f1)(x);
{}

lemma void mplus_assoc<t>(fixpoint(t, int) f1, fixpoint(t, int) f2, fixpoint(t, int) f3, t x)
    requires true;
    ensures mplus(f1, mplus(f2, f3))(x) == mplus(mplus(f1, f2), f3)(x);
{}

lemma void count_eq_cons<t>(t h, list<t> t, t x)
    requires true;
    ensures count_eq(cons(h, t), x) == (h == x ? 1 : 0) + count_eq(t, x);
{}

lemma void forall_lt_append(list<int> l1, list<int> l2, int p)
    requires forall(l1, (lt)(p)) == true &*& forall(l2, (lt)(p)) == true;
    ensures forall(append(l1, l2), (lt)(p)) == true;
{
    forall_append(l1, l2, (lt)(p));
}

lemma void forall_ge_append(list<int> l1, list<int> l2, int p)
    requires forall(l1, (ge)(p)) == true &*& forall(l2, (ge)(p)) == true;
    ensures forall(append(l1, l2), (ge)(p)) == true;
{
    forall_append(l1, l2, (ge)(p));
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
      forall(vslow, (lt)(vpivot)) == true &*&
      forall(vshigh, (ge)(vpivot)) == true &*&
      (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
  @*/
{
  //@ ints_split(a, hi);
  //@ assert a[lo..hi] |-> ?vs_body &*& a[hi] |-> ?pivot;
  //@ append_take_drop_n(vs, hi - lo);
  
  int pivot_val = a[hi];
  
  int i = lo - 1;
  int j;

  //@ ints_split(a, lo);
  //@ assert a[lo..lo] |-> nil &*& a[lo..hi] |-> vs_body;
  
  for (j = lo; j < hi; j++)
    /*@
    invariant
        lo <= j &*& j <= hi &*&
        lo - 1 <= i &*& i < j &*&
        a[lo..i + 1] |-> ?v_lt &*&
        a[i + 1..j] |-> ?v_ge &*&
        a[j..hi] |-> ?v_rest &*&
        a[hi] |-> pivot_val &*&
        forall(v_lt, (lt)(pivot_val)) == true &*&
        forall(v_ge, (ge)(pivot_val)) == true &*&
        (mplus)((count_eq)(v_lt), (mplus)((count_eq)(v_ge), (count_eq)(append(v_rest, cons(pivot_val, nil))))) == (count_eq)(vs);
    @*/
  {
    //@ ints_split(a + j, 1);
    //@ assert a[j] |-> ?aj;
    //@ assert a[j+1..hi] |-> ?v_rest_tail;
    int aj_val = a[j];
    if (aj_val < pivot_val) {
      i++;
      //@ ints_split(a, i);
      //@ assert a[lo..i] |-> ?v_lt_old;
      //@ assert a[i..j] |-> ?v_ge_old;
      
      if (i < j) {
        //@ ints_split(a + i, 1);
        //@ assert a[i] |-> ?v_i;
        //@ assert a[i+1..j] |-> ?v_mid;
        swap(a, i, j);
        //@ ints_join(a + i);
        //@ forall_append_inv(v_ge_old, (ge)(pivot_val));
        //@ forall_ge_append(v_mid, cons(v_i, nil), pivot_val);
      }
      //@ ints_join(a);
      //@ assert a[lo..i+1] |-> ?v_lt_new;
      //@ assert a[i+1..j+1] |-> ?v_ge_new;
      //@ forall_lt_append(v_lt_old, cons(aj_val, nil), pivot_val);
      
      /*@
      {
          fixpoint(int, int) f_lt_old = (count_eq)(v_lt_old);
          fixpoint(int, int) f_ge_old = (count_eq)(v_ge_old);
          fixpoint(int, int) f_rest_old = (count_eq)(append(v_rest, cons(pivot_val, nil)));
          
          fixpoint(int, int) f_lt_new = (count_eq)(v_lt_new);
          fixpoint(int, int) f_ge_new = (count_eq)(v_ge_new);
          fixpoint(int, int) f_rest_new = (count_eq)(append(v_rest_tail, cons(pivot_val, nil)));
          
          int z = 0;
          if (i < j) {
              list<int> v_ge_mid = drop(1, v_ge_old);
              count_eq_append(v_lt_old, cons(aj_val, nil), z);
              count_eq_append(v_ge_mid, cons(head(v_ge_old), nil), z);
              count_eq_cons(head(v_ge_old), v_ge_mid, z);
              count_eq_cons(aj_val, v_rest_tail, z);
          } else { // i == j
              count_eq_append(v_lt_old, cons(aj_val, nil), z);
              count_eq_cons(aj_val, v_rest_tail, z);
          }
          forall_t_elim(forall_int, (mplus_assoc)(f_lt_old, f_ge_old, f_rest_old), z);
          forall_t_elim(forall_int, (mplus_assoc)(f_lt_new, f_ge_new, f_rest_new), z);
          assert (mplus(f_lt_new, mplus(f_ge_new, f_rest_new)))(z) == (mplus(f_lt_old, mplus(f_ge_old, f_rest_old)))(z);
      }
      @*/
    } else {
      //@ ints_join(a + j);
      //@ assert a[i+1..j+1] |-> ?v_ge_new;
      //@ forall_ge_append(v_ge, cons(aj_val, nil), pivot_val);
      /*@
      {
          fixpoint(int, int) f_lt_old = (count_eq)(v_lt);
          fixpoint(int, int) f_ge_old = (count_eq)(v_ge);
          fixpoint(int, int) f_rest_old = (count_eq)(append(v_rest, cons(pivot_val, nil)));
          
          fixpoint(int, int) f_lt_new = (count_eq)(v_lt);
          fixpoint(int, int) f_ge_new = (count_eq)(v_ge_new);
          fixpoint(int, int) f_rest_new = (count_eq)(append(v_rest_tail, cons(pivot_val, nil)));
          
          int z = 0;
          count_eq_append(v_ge, cons(aj_val, nil), z);
          count_eq_cons(aj_val, v_rest_tail, z);
          forall_t_elim(forall_int, (mplus_assoc)(f_lt_old, f_ge_old, f_rest_old), z);
          forall_t_elim(forall_int, (mplus_assoc)(f_lt_new, f_ge_new, f_rest_new), z);
          assert (mplus(f_lt_new, mplus(f_ge_new, f_rest_new)))(z) == (mplus(f_lt_old, mplus(f_ge_old, f_rest_old)))(z);
      }
      @*/
    }
  }
  
  //@ assert a[lo..i + 1] |-> ?v_lt &*& a[i + 1..hi] |-> ?v_ge &*& a[hi] |-> pivot_val;
  i++;
  //@ ints_split(a, i);
  //@ assert a[lo..i] |-> v_lt;
  //@ assert a[i..hi] |-> v_ge;
  
  if (i < hi) {
    //@ ints_split(a + i, 1);
    //@ assert a[i] |-> ?v_i;
    //@ assert a[i+1..hi] |-> ?v_ge_tail;
    swap(a, i, hi);
    //@ ints_join(a + i);
    //@ assert a[i+1..hi+1] |-> ?vshigh;
    //@ forall_append_inv(v_ge, (ge)(pivot_val));
    //@ forall_ge_append(v_ge_tail, cons(v_i, nil), pivot_val);
    /*@
    {
        int z = 0;
        list<int> vslow = v_lt;
        int vpivot = pivot_val;
        count_eq_append(v_ge_tail, cons(v_i, nil), z);
        count_eq_cons(v_i, v_ge_tail, z);
        count_eq_cons(vpivot, vshigh, z);
        count_eq_cons(pivot_val, nil, z);
        assert (mplus((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))))(z) == (mplus((count_eq)(v_lt), (mplus)((count_eq)(v_ge), (count_eq)(cons(pivot_val, nil)))))(z);
    }
    @*/
  } else { // i == hi
    //@ assert v_ge == nil;
    /*@
    {
        int z = 0;
        count_eq_cons(pivot_val, nil, z);
        assert (mplus((count_eq)(v_lt), (count_eq)(cons(pivot_val, nil))))(z) == (mplus((count_eq)(v_lt), (mplus)((count_eq)(v_ge), (count_eq)(cons(pivot_val, nil)))))(z);
    }
    @*/
  }
  //@ ints_join(a);
  return i;
}