#include <stdint.h>
#include <stdbool.h>

/***
 * Description:
 * The `inc` function increments the value stored at the memory location 
 * pointed to by `i`.
 *
 * @param i - A pointer to an integer variable that should be incremented.
 *
 * The function reads the current value, increases it by 1, and stores the new value.
 */
void inc(int* i)
{
  (*i) = (*i) + 1;
}

/***
 * Description:
 * The `inc_uintptr_t` function increments a `uintptr_t` value stored at the given pointer.
 *
 * @param i - A pointer to a `uintptr_t` variable that should be incremented.
 *
 * The function retrieves the current value, increases it by 1, and updates the variable.
 */
void inc_uintptr_t(uintptr_t *i)
{
  (*i) = (*i) + 1;
}

/***
 * Description:
 * The `address_of_param` function demonstrates passing a local variable’s address.
 *
 * @param x - A local integer variable.
 *
 * The function sets `x` to `5`, assigns its address to a pointer, increments it,
 * and asserts that the final value is `6`.
 */
void address_of_param(int x) 
{
    x = 5;
    int* ptr = &x; 
    inc(ptr);
    int z = x;
    assert(z == 6);
}

/***
 * Description:
 * The `address_of_local` function demonstrates the use of pointers 
 * and pointer-to-pointer relationships.
 *
 * It creates a local integer, stores its address in a pointer, then 
 * a pointer to that pointer, and increments the original variable.
 * The function asserts that the final value is `1`.
 */
void address_of_local() 
{
  int x = 0;
  {
    int* ptr = &x;
    {
      int** ptrptr = &ptr;
      inc(*ptrptr);
      int z = x;
      assert(z == 1);
    }
  }
  return;
}

/***
 * Description:
 * The `address_of_local_uintptr_t` function is similar to `address_of_local`
 * but uses `uintptr_t` instead of an integer.
 *
 * It initializes a `uintptr_t` variable, stores its address in a pointer, 
 * then creates a pointer to that pointer, increments the original variable,
 * and asserts that its final value is `1`.
 */
void address_of_local_uintptr_t() 
{
  uintptr_t x = 0;
  {
    uintptr_t* ptr = &x;
    {
      uintptr_t** ptrptr = &ptr;
      inc_uintptr_t(*ptrptr);
      uintptr_t z = x;
      assert(z == 1);
    }
  }
  return;
}
