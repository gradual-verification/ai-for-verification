/***
 * Function: is_even_nat
 *
 * Description:
 * Determines whether a non-negative integer `x` is even using recursion.
 *
 * Base cases:
 * - If `x == 0`, the number is even → returns `true`.
 * - If `x == 1`, the number is odd  → returns `false`.
 *
 * Recursive case:
 * - For values greater than 1, the function calls itself with `x - 2`.
 *
@param x - the integer to be tested for evenness.
@return `true` if `x` is even, `false` otherwise.
 */
bool is_even_nat(int x)
{
  if(x == 0)
    return true;
  else if(x == 1)
    return false;
  else {
    return is_even_nat(x - 2);
  }
}