#include "malloc.h"

/***
 * Description:
The set_to_zero function sets 0 to the elements in an array 
of a given length and pointed to by a given pointer.

@param a: the pointer pointing to an array
@param N: the length of the array

It makes sure that the array has its N elements to be 0. 
*/
void set_to_zero(int* a, int N) 
{
  int k = 0;
  while(k < N) 
  {
    a[k] = 0;
    k++;
  }
}

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
