typedef int my_int;

/***
 * Description:
The function performs some arithmetic operations.

@param none

Within this function, a variable `x` of type `my_int`
(typedef for `int`) is declared and initialized with
the value 5. Another variable `y` of type `int` is then
assigned the value of `x`. Likewise, a variable `z` of
type `my_int` is declared and assigned the value 3.
Additionally, a variable `t` of type `my_int` is declared
and assigned the sum of `x` and `z`. Finally, an assertion
is made to ensure that `t` is equal to 8 before the function
returns 0.

*/
int main()
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    assert(t == 8);
    return 0;
}
