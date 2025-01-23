#include "verifast.h"

/*@
predicate valid_int(int* p) = integer(p, _);
@*/

/***
 * Description: 
 * The sum_of_range function calculates the sum of all integers in the range from 0 to n-1.
 * 
 * @param `n` - the upper limit of the range (exclusive).
 * 
 * It requires: The parameter `n` must be a non-negative integer.
 * It ensures: The result is equal to the sum of all integers in the range from 0 to n-1.
 */

/*@
requires n >= 0;
requires valid_int(&n);
ensures \result == (n * (n - 1)) / 2;
@*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    /*@
    loop_invariant 0 <= count <= n;
    loop_invariant sum == (count * (count - 1)) / 2;
    loop_invariant valid_int(&count) && valid_int(&sum);
    @*/
    while (count != n)
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

int main()
{
    return 0;
}
