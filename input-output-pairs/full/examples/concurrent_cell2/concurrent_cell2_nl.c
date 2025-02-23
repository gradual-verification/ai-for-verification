/*atomic_dec function
-param: c: pointer to the cell
-description: atomically decrement the value of the cell
*/
void atomic_dec(int* c);

/*atomic_load function
-param: c: pointer to the cell
-description: atomically load the value of the cell
*/
int atomic_load(int* c);

/*atomic_cas function
-param: c: pointer to the cell
-param: old: old value of the cell
-param: new: new value of the cell
-description: atomically compare the value of the cell with the old value and if it is equal to the old value, set the value of the cell to the new value
*/
int atomic_cas(int* c, int old, int new);


/*acquire function
-param: c: pointer to the cell
-description: acquire the cell by incrementing the value of c
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
-description: release the cell by decrementing the value of c
*/
void release(int* c)
{
  atomic_dec(c);
}
