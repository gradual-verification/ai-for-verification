//@ #include <arrays.gh> // For ints_split and ints_join
//@ #include <quantifiers.gh> // For not_forall and forall_elim


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


void quicksort(int *a, int lo, int hi)
  //@ requires lo >= 0 &*& a[lo..hi + 1] |-> ?vs;
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

