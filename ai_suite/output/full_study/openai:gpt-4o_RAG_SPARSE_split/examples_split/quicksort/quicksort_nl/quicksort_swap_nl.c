#include "prelude.h"

//@ #include "list.gh"

//@ predicate array(int *a, int n; list<int> vs) = ints(a, n, vs);

/*@
  requires
    array(a, ?n, ?vs) &*&
    0 <= i &*& i < n &*&
    0 <= j &*& j < n;
  ensures
    array(a, n, ?vs2) &*&
    nth(i, vs2) == nth(j, vs) &*&
    nth(j, vs2) == nth(i, vs) &*&
    forall(k; 0 <= k && k < n && k != i && k != j ==> nth(k, vs2) == nth(k, vs));
@*/
void swap(int *a, int i, int j)
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}