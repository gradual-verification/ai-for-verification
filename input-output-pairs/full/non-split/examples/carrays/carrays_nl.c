#include <stdio.h>

/***
 * Description:
 * The `array_test1` function reads three consecutive integer values from an array.
 *
 * @param a - A pointer to an array containing at least 3 elements.
 *
 * The function makes sure that the array is not changed.
 */
void array_test1(int* a)
{
    int tmp0 = a[0];
    int tmp1 = a[1];
    int tmp2 = a[2];
}

/***
 * Description:
 * The `array_test2` function modifies the first element of the array to `10` and reads its second element. 
 * 
 * @param a - A pointer to an array of at least two elements.
 *
 * The function\ makes sure that a[0] is updated to 10 and other elements are unchanged. 
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
 * predefined array {0, 10, 20, 30, 40, 50, 60, 70, 80, 90} and returns its previous value.
 *
 * @param arr - A pointer to an array of at least 10 integers.
 * 
 * It makes sure that the return value is the original value of `arr[3]` before incrementing (i.e., 30),
 * and arr is modified to {0, 10, 20, 31, 40, 50, 60, 70, 80, 90}.
 */
int to_verify(int* arr)
{
    return arr[3]++;
}
