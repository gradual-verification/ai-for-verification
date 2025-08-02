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


// TODO: make this function pass the verification
/*acquire function
-param: c: pointer to the cell
-description: acquire the lock by compare-and-swaping the value of c with 0 to 1. 

It ensures that in the end, the lock is acquired by the current thread.
*/
void acquire(int* c)
//@ requires integer(c, ?v);
//@ ensures integer(c, 1) &*& v == 0 || v == 1;
{
  while(true)
    //@ invariant integer(c, ?cv) &*& cv == 0 || cv == 1;
  {
    int read = atomic_cas(c, 0, 1);
    if(read == 0) {
      break;
    }
  }
}