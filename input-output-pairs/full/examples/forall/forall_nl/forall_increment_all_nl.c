

// TODO: make this function pass the verification
/***
 * Description:
The increment_all function increments all elements by 1 in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes suer that the array has its N elements incremented by 1.
*/
void increment_all(int* a, int N) 
{
  int k = 0;
  while(k < N)
  {
    a[k] = a[k] + 1;
    k++;
  }
}
