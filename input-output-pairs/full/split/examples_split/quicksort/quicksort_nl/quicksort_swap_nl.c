
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
{
    int aj = a[j];
    a[j] = a[i];
    a[i] = aj;
}

