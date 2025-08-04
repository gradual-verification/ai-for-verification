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

// Helper fixpoints and lemmas for quicksort verification

fixpoint bool le_option(int x, option<int> y) {
    switch (y) {
        case none: return true;
        case some(y0): return x <= y0;
    }
}

fixpoint bool ge_option(int x, option<int> y) {
    switch (y) {
        case none: return true;
        case some(y0): return x >= y0;
    }
}

lemma void forall_le_le_option(list<int> vs, int upper)
    requires forall(vs, (le)(upper)) == true;
    ensures forall(vs, (le_option)(some(upper))) == true;
{
    switch (vs) {
        case nil:
        case cons(h, t):
            forall_elim(vs, (le)(upper), h);
            forall_le_le_option(t, upper);
    }
}

lemma void forall_ge_ge_option(list<int> vs, int lower)
    requires forall(vs, (ge)(lower)) == true;
    ensures forall(vs, (ge_option)(some(lower))) == true;
{
    switch (vs) {
        case nil:
        case cons(h, t):
            forall_elim(vs, (ge)(lower), h);
            forall_ge_ge_option(t, lower);
    }
}

lemma void is_sorted_between_some_none_implies_sorted(list<int> vs, int lower)
    requires is_sorted_between(some(lower), vs, none) == true;
    ensures is_sorted_between(none, vs, none) == true;
{
    switch(vs) {
        case nil:
        case cons(h,t):
            open is_sorted_between(some(lower), vs, none);
            is_sorted_between_some_none_implies_sorted(t, h);
            close is_sorted_between(none, vs, none);
    }
}

lemma void is_sorted_between_weaken_upper(list<int> vs, option<int> upper)
    requires is_sorted_between(none, vs, none) == true &*& forall(vs, (le_option)(upper)) == true;
    ensures is_sorted_between(none, vs, upper) == true;
{
    switch (vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(none, vs, none);
            is_sorted_between_some_none_implies_sorted(t, h);
            is_sorted_between_weaken_upper(t, upper);
            close is_sorted_between(none, vs, upper);
    }
}

lemma void is_sorted_between_weaken_lower(list<int> vs, option<int> lower)
    requires is_sorted_between(none, vs, none) == true &*& forall(vs, (ge_option)(lower)) == true;
    ensures is_sorted_between(lower, vs, none) == true;
{
    switch (vs) {
        case nil:
        case cons(h, t):
            open is_sorted_between(none, vs, none);
            close is_sorted_between(lower, vs, none);
    }
}

lemma void is_sorted_between_append(list<int> vs1, int pivot, list<int> vs2)
    requires is_sorted_between(none, vs1, some(pivot)) == true &*& is_sorted_between(some(pivot), vs2, none) == true;
    ensures is_sorted_between(none, append(vs1, cons(pivot, vs2)), none) == true;
{
    switch (vs1) {
        case nil:
            open is_sorted_between(none, nil, some(pivot));
            close is_sorted_between(none, cons(pivot, vs2), none);
        case cons(h, t):
            open is_sorted_between(none, vs1, some(pivot));
            is_sorted_between_append(t, pivot, vs2);
            close is_sorted_between(none, append(vs1, cons(pivot, vs2)), none);
    }
}

lemma void mem_count_eq<t>(t x, list<t> xs)
    requires true;
    ensures mem(x, xs) == (count_eq(xs, x) > 0);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            mem_count_eq(x, t);
    }
}

lemma void forall_from_count_eq<t>(list<t> l1, list<t> l2, fixpoint(t, bool) p)
    requires (count_eq)(l1) == (count_eq)(l2) &*& forall(l1, p) == true;
    ensures forall(l2, p) == true;
{
    if (!forall(l2, p)) {
        t witness = not_forall(l2, p);
        assert !p(witness);
        mem_count_eq(witness, l2);
        assert count_eq(l2, witness) > 0;
        assert count_eq(l1, witness) > 0;
        mem_count_eq(witness, l1);
        forall_elim(l1, p, witness);
        assert false;
    }
}

fixpoint bool count_eq_property<t>(fixpoint(t, int) f1, fixpoint(t, int) f2, t x) {
    return f1(x) == f2(x);
}

lemma void forall_t_elim_int(fixpoint(int, bool) p, int x)
    requires forall_int(p) == true;
    ensures p(x) == true;
{
    get_forall_int();
    forall_t_elim(forall_int, p, x);
}

lemma void count_eq_spec_lemma(list<int> vslow_sorted, list<int> vslow, list<int> vshigh_sorted, list<int> vshigh, int vpivot, list<int> vs)
    requires
        (count_eq)(vslow_sorted) == (count_eq)(vslow) &*&
        (count_eq)(vshigh_sorted) == (count_eq)(vshigh) &*&
        (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);
    ensures
        (count_eq)(append(vslow_sorted, cons(vpivot, vshigh_sorted))) == (count_eq)(vs);
{
    fixpoint(int, int) f1 = (count_eq)(append(vslow_sorted, cons(vpivot, vshigh_sorted)));
    fixpoint(int, int) f2 = (count_eq)(vs);
    if (f1 != f2) {
        get_forall_int();
        if (!forall_int((count_eq_property)(f1, f2))) {
            int witness = not_forall_int((count_eq_property)(f1, f2));
            count_append(vslow_sorted, cons(vpivot, vshigh_sorted), (eq)(witness));
            count_append(cons(vpivot, nil), vshigh_sorted, (eq)(witness));
            assert f1(witness) == count_eq(vslow_sorted, witness) + count_eq(cons(vpivot, nil), witness) + count_eq(vshigh_sorted, witness);
            assert f1(witness) == count_eq(vslow, witness) + count_eq(cons(vpivot, nil), witness) + count_eq(vshigh, witness);
            count_append(cons(vpivot, nil), vshigh, (eq)(witness));
            assert f1(witness) == count_eq(vslow, witness) + count_eq(cons(vpivot, vshigh), witness);
            assert f1(witness) == mplus((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh)), witness);
            assert f1(witness) == f2(witness);
            assert false;
        }
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
  
  int pivot = a[hi];
  
  int i = lo - 1;
  int j;

  for (j = lo; j < hi; j++)
    //@ requires a[lo..i+1] |-> ?small &*& a[i+1..j] |-> ?large &*& a[j..hi] |-> ?rest &*& a[hi] |-> pivot &*& forall(small, (le)(pivot)) == true &*& forall(large, (ge)(pivot)) == true;
    //@ ensures a[lo..old_i+1] |-> ?small2 &*& a[old_i+1..j+1] |-> ?large2 &*& a[j+1..hi] |-> ?rest2 &*& a[hi] |-> pivot &*& forall(small2, (le)(pivot)) == true &*& forall(large2, (ge)(pivot)) == true;
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
  if (lo >= hi) {
    if (lo > hi) {
        //@ ints_to_nil(a + lo, hi + 1 - lo);
    } else { // lo == hi
        //@ open a[lo..hi+1] |-> ?vsh;
        //@ is_sorted_between_some_none_implies_sorted(nil, head(vsh));
        //@ close is_sorted_between(none, vsh, none);
    }
    return;
  } else {
    int p = partition(a, lo, hi);
    
    //@ assert a[lo..p] |-> ?vslow &*& a[p..p+1] |-> cons(?vpivot, nil) &*& a[p+1..hi+1] |-> ?vshigh;
    //@ assert forall(vslow, (le)(vpivot)) == true;
    //@ assert forall(vshigh, (ge)(vpivot)) == true;
    //@ assert (mplus)((count_eq)(vslow), (count_eq)(cons(vpivot, vshigh))) == (count_eq)(vs);

    quicksort(a, lo, p - 1);
    //@ assert a[lo..p] |-> ?vslow_sorted &*& (count_eq)(vslow_sorted) == (count_eq)(vslow) &*& is_sorted_between(none, vslow_sorted, none) == true;

    quicksort(a, p + 1, hi);
    //@ assert a[p+1..hi+1] |-> ?vshigh_sorted &*& (count_eq)(vshigh_sorted) == (count_eq)(vshigh) &*& is_sorted_between(none, vshigh_sorted, none) == true;

    //@ ints_join(a + lo);
    //@ ints_join(a + lo);
    
    //@ list<int> vs2 = append(vslow_sorted, cons(vpivot, vshigh_sorted));
    //@ count_eq_spec_lemma(vslow_sorted, vslow, vshigh_sorted, vshigh, vpivot, vs);
    
    //@ forall_from_count_eq(vslow, vslow_sorted, (le)(vpivot));
    //@ forall_le_le_option(vslow_sorted, vpivot);
    //@ is_sorted_between_weaken_upper(vslow_sorted, some(vpivot));

    //@ forall_from_count_eq(vshigh, vshigh_sorted, (ge)(vpivot));
    //@ forall_ge_ge_option(vshigh_sorted, vpivot);
    //@ is_sorted_between_weaken_lower(vshigh_sorted, some(vpivot));

    //@ is_sorted_between_append(vslow_sorted, vpivot, vshigh_sorted);
  }
}