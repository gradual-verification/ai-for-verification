/*atomic_dec function
-param: c: pointer to the cell
-description: atomically decrement the value of the cell. 

It doesn't have any implementation.

It ensures that this decrement operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation). 
*/
void atomic_dec(int* c);

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load and return the value of the cell.

It doesn't have any implementation.

It ensures that this load operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation). 
*/
int atomic_load(int* c);

/*atomic_cas function
-param: c: pointer to the cell
-param: old: old value of the cell
-param: new: new value of the cell
-description: atomically compare the value of the cell with the old value and if it is equal to the old value, set the value of the cell to the new value. 
It returns the old value of the cell. 

It doesn't have any implementation.

It ensures that this compare-and-swap operation must finish at the end 
(while operations of other threads can be finished concurrently during this operation). 
Its returns the old value of the cell.
*/
int atomic_cas(int* c, int old, int new);

/*only_allow_incrementing function
-param: c: pointer to the cell
-description: check whether only incrementing operation is done on a cell. 

It uses an assert statement to show that two loads doesn't decrement the value. 
*/
void only_allow_incrementing(int* c)
{
  int x1 = atomic_load(c);
  int x2 = atomic_load(c);
  assert x1 <= x2;
}

/*acquire function
-param: c: pointer to the cell
-description: acquire the lock by compare-and-swaping the value of c with 0 to 1. 
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
*/
void release(int* c)
{
  atomic_dec(c);
}
