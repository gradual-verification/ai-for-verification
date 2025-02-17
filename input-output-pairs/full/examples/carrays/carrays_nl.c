#include <stdio.h>

/***
 * Description:
 * The `array_test1` function reads three consecutive integer values from an array.
 *
 * @param a - A pointer to an array containing at least 3 elements.
 *
 * The function reads the first three elements of the array into temporary variables.
 */
void array_test1(int* a)
{
    int tmp0 = a[0];
    int tmp1 = a[1];
    int tmp2 = a[2];
}

/***
 * Description:
 * The `array_test2` function modifies the first element of the array to `10`
 * while ensuring the second element remains unchanged.
 *
 * @param a - A pointer to an array of at least two elements.
 *
 * The function updates `a[0]` to `10`, asserts the value is correctly set,
 * and verifies that `a[1]` retains its original value.
 */
void array_test2(int* a)
{
    int a1_old = a[1];  
    a[0] = 10;          
    int tmp = a[0];     
    assert(tmp == 10);  
    int a1 = a[1];
    assert(a1_old == a1); 
}

/***
 * Description:
 * The `to_verify` function increments the fourth element (`arr[3]`) of a 
 * predefined array and returns its previous value.
 *
 * @param arr - A pointer to an array of at least 10 integers.
 * @returns The original value of `arr[3]` before incrementing.
 */
int to_verify(int* arr)
{
    return arr[3]++;
}
