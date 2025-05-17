/***
 * Function: foo
 *
 * Description:
 * Takes an integer `x` and verifies through assertions that it falls within valid `int` range boundaries.
 *
@param x - an integer to be checked against `INT_MIN` and `INT_MAX`.
 */
void foo(int x)
{
    assert(INT_MIN <= x);
    assert(x <= INT_MAX);
}