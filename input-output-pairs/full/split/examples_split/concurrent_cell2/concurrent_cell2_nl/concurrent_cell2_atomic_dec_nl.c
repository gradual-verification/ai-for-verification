
// TODO: make this function pass the verification
/*atomic_dec function
-param: c: pointer to the cell
-description: atomically decrement the value of the cell. 

It doesn't have any implementation.

It requires that the decrement operation is allowed on the cell.
It ensures that this decrement operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation),
so the old trace is the prefix of current trace.
*/
void atomic_dec(int* c);

