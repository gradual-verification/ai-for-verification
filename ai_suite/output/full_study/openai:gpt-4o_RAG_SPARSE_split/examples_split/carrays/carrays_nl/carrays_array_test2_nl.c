#include <stdio.h>

//@ #include "arrays.gh"

// TODO: make this function pass the verification
/***
 * Description:
 * The `array_test2` function modifies the first element of the array to `10` and reads its second element. 
 * 
 * @param a - A pointer to an array of at least two elements.
 *
 * The function makes sure that a[0] is updated to 10 and other elements are unchanged. 
 */
//@ requires ints(a, 2, ?values);
//@ ensures ints(a, 2, cons(10, cons(nth(1, values), nil)));
void array_test2(int* a)
{
    int a1_old = a[1];  
    a[0] = 10;          
    int tmp = a[0];     
    assert(tmp == 10);  
    int a1 = a[1];
    assert(a1_old == a1); 
}