// TODO: make this function pass the verification
/*** 
 * Description:
The swap function exchanges the values at indices i and j in the integer array `a`.

@param - 
a - A pointer to an integer array in memory.
i - A valid index within the array.
j - A valid index within the array.

@requires - 
Indices i and j must be within the bounds of the array.

@ensures - 
Exchanges the values at positions i and j in the array. No value is returned.
*/
void swap(int *a, int i, int j)
//@ requires a != 0 &*& i >= 0 &*& j >= 0 &*& ints(a + i, 1, ?vi) &*& ints(a + j, 1, ?vj);
//@ ensures ints(a + i, 1, ?vi_new) &*& ints(a + j, 1, ?vj_new) &*& vi_new == vj &*& vj_new == vi;
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}