/***
 * Description:
 * The `test` function initializes an integer `x` with a large value and 
 * attempts to add `x` to itself.
 *
 * @param none
 */

void test()
{
    int x = 30000;
    x = x + x; //~ should_fail
}
