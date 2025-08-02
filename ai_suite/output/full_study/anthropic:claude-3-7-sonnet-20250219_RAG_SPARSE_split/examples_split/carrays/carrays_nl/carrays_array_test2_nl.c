#include <stdio.h>


// TODO: make this function pass the verification
/***
 * Description:
 * The `array_test2` function modifies the first element of the array to `10` and reads its second element. 
 * 
 * @param a - A pointer to an array of at least two elements.
 *
 * The function\ makes sure that a[0] is updated to 10 and other elements are unchanged. 
 */
void array_test2(int* a)
//@ requires a != 0 &*& ints(a, 2, ?vs);
//@ ensures ints(a, 2, cons(10, tail(vs)));
{
    int a1_old = a[1];  
    a[0] = 10;          
    int tmp = a[0];     
    assert(tmp == 10);  
    int a1 = a[1];
    //@ assert a1 == a1_old;
    assert(a1_old == a1); 
}