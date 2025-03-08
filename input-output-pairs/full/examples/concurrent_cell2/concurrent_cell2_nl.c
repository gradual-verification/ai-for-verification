/*atomic_dec function
-param: c: pointer to the cell
-description: atomically decrement the value of the cell. 

It doesn't have any implementation.

It requires the cell has a function that allows the decrement operation, and there is an old trace before this operation. 
It ensures the cell keeps the same function, having a current trace starting being decremented on, 
and the old trace is a prefix of current trace from the perspective of this thread. 
*/
void atomic_dec(int* c);

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load the value of the cell. 

It doesn't have any implementation.

It requires the cell has a function that allows such operation, and there is an old trace before this operation. 
It ensures the cell keeps the same function, having a current trace, 
and the old trace is a prefix of current trace from the perspective of this thread, 
and the result can be calculated by executing the current trace.
*/
int atomic_load(int* c);

/*atomic_cas function
-param: c: pointer to the cell
-param: old: old value of the cell
-param: new: new value of the cell
-description: atomically compare the value of the cell with the old value and if it is equal to the old value, set the value of the cell to the new value. 
It returns the old value of the cell. 

It doesn't have any implementation.

It requires the cell has a function that allows the compare-and-swap operation, and there is an old trace before this operation. 
It ensures the cell keeps the same function, having a new trace being compare-and-swapped on, 
and the old trace is a prefix of current trace from the perspective of this thread, 
and the result can be calculated by executing the current trace.
*/
int atomic_cas(int* c, int old, int new);

/*only_allow_incrementing function
-param: c: pointer to the cell
-description: check whether only incrementing operation is done on a cell. 

It requires that the cell has a function that allows the increment-only operation, and there is an old trace on it. 
It ensures that the function is not changed and a new trace will be seen. 
*/
void only_allow_incrementing(int* c)
{
  int x1 = atomic_load(c);
  int x2 = atomic_load(c);
  assert x1 <= x2;
}

/*acquire function
-param: c: pointer to the cell
-description: acquire the lock by compare-and-swap the value of c with 0 to 1. 

It requires the cell has a function that allows the trace of operation to act as a lock, 
and there is an old trace before this operation. 
It ensures the cell keeps the same function, having a new trace , 
with the lock owner of the trace as the current thread. 
*/
void acquire(int* c)
{
  while(true)
    
  {
    int read = atomic_cas(c, 0, 1);
    if(read == 0) {
      break;
    }
  }
}

/*release function
-param: c: pointer to the cell
-description: release the lock by decrementing the value of c

It requires the cell has a function that allows the trace of operation to act as a lock, 
and there is an old trace before this operation, and the lock owner of the old trace is current thread. 
It ensures the cell keeps the same function, having a new trace , 
with the lock owner of the trace as none. 
*/
void release(int* c)
{
  atomic_dec(c);
}
