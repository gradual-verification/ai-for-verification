
// TODO: make this function pass the verification
/*atomic_cas function
-param: c: pointer to the cell
-param: old: old value of the cell
-param: new: new value of the cell
-description: atomically compare the value of the cell with the old value and if it is equal to the old value, set the value of the cell to the new value. 
It returns the old value of the cell. 

It doesn't have any implementation.

It requires that the cas operation is allowed on the cell.
It ensures that this compare-and-swap operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation), 
so the old trace is the prefix of current trace.
Its returns the old value of the cell.
*/
int atomic_cas(int* c, int old, int new);

