/*@
fixpoint int add_one(int x) { return x + 1; }

lemma void map_append<a, b>(fixpoint(a, b) f, list<a> xs, list<a> ys)
    requires true;
    ensures map(f, append(xs, ys)) == append(map(f, xs), map(f, ys));
{
    switch(xs) {
        case nil:
        case cons(h, t):
            map_append(f, t, ys);
    }
}

lemma void take_plus_one<t>(int k, list<t> xs)
    requires 0 <= k && k < length(xs);
    ensures take(k + 1, xs) == append(take(k, xs), cons(nth(k, xs), nil));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (k == 0) {
            } else {
                take_plus_one(k - 1, t);
            }
    }
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The increment_all function increments all elements by 1 in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes suer that the array has its N elements incremented by 1.
*/
void increment_all(int* a, int N)
    //@ requires 0 <= N &*& ints(a, N, ?vs);
    //@ ensures ints(a, N, map(add_one, vs));
{
  int k = 0;
  while(k < N)
    //@ invariant 0 <= k &*& k <= N &*& ints(a, k, map(add_one, take(k, vs))) &*& ints(a + k, N - k, drop(k, vs));
  {
    //@ open ints(a + k, N - k, drop(k, vs));
    a[k] = a[k] + 1;
    //@ take_plus_one(k, vs);
    //@ map_append(add_one, take(k, vs), cons(nth(k, vs), nil));
    //@ ints_join(a);
    k++;
  }
}