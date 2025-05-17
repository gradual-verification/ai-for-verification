/***
 * Struct: cell
 *
 * Description:
 * A wrapper structure containing a single integer field `x`.
 */
struct cell {
  int x;
};

/***
 * Function: m
 *
 * Description:
 * A simple test function that verifies the internal invariant of the `cell`
 * (i.e., that the value `v` inside the cell is non-negative).
 * It does so using the `assert` directive, relying on `cell_pos` to be applied automatically.
 *
@param c - a pointer to a `struct cell` whose value is tracked and verified.
 */
void m(struct cell *c)
{
  //@ assert 0 <= v;
}