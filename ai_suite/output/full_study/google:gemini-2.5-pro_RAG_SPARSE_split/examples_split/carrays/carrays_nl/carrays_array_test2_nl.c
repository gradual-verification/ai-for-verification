#include <stdio.h>
#include <assert.h>

/*@
#include <list.gh>
@*/

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
    //@ requires ints(a, ?N, ?vs) &*& N >= 2;
    //@ ensures ints(a, N, update(0, 10, vs));
{
    int a1_old = a[1];  
    a[0] = 10;          
    int tmp = a[0];     
    assert(tmp == 10);  
    int a1 = a[1];
    assert(a1_old == a1); 
}