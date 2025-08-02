/***
 * Description:
 * The `inc` function increments the value stored at the memory location 
 * pointed to by `i`.
 *
 * @param i - A pointer to an integer variable that should be incremented.
 *
 * The function makes sure that the value at i is incremented by 1.
 */

/*@
  requires integer(i, ?v);
  ensures integer(i, v + 1);
@*/
void inc(int* i)
{
  (*i) = (*i) + 1;
}