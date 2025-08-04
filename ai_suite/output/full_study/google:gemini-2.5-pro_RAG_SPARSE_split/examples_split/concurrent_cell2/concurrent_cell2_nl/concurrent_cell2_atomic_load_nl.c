// TODO: make this function pass the verification
/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that the old trace is the prefix of current trace.
*/
/*@
requires integer(c, ?v);
ensures integer(c, v) &*& result == v;
@*/
int atomic_load(int* c);