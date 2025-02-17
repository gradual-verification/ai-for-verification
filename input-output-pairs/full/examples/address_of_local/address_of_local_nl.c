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

/***
 * Description:
 * The `test_goto` function demonstrates the `goto` statement.
 *
 * The function jumps to the `end` label, skipping a block of 
 * dead code that would otherwise assign values and abort execution.
 */
void test_goto() 
{
  goto end;
  {
    int x = 5;
    int *p = &x;
    abort();
  }
  end:
}

/***
 * Description:
 * The `test_goto2` function declares a local variable and a pointer
 * and then jumps to a label `end`, effectively skipping execution 
 * after initialization.
 */
void test_goto2()
{
  {
    int x = 0;
    int* ptr = &x;
    goto end;
  }
  end:
}

/***
 * Description:
 * The `test_goto3` function initializes an integer and a pointer,
 * then jumps to a label and modifies the value of `x` after the jump.
 */
void test_goto3()
{
  {
    int x = 0;
    int* ptr = &x;
    goto next;
    next:
    x = 3;
  }
}

/***
 * Description:
 * The `test_break` function demonstrates breaking out of a while loop.
 *
 * The function enters an infinite loop but immediately declares a local
 * variable and breaks out of the loop.
 */
void test_break()
{
  while(true) 
  {
    int x = 0;
    int* ptr = &x;
    break;
  }
}

/***
 * Description:
 * The `test_break2` function is similar to `test_break`, but explicitly 
 * states `requires` and `ensures` conditions for the loop.
 *
 * The function initializes an integer and breaks out of the loop after
 * the first iteration.
 */
void test_break2()
{
  while(true) 
  {
      int x = 0;
      int* ptr = &x;
      break;
  }
}

/***
 * Description:
 * The `test_requires_ensures_loop` function demonstrates a while loop 
 * with conditions on its variable.
 *
 * The loop runs while `i < 5`, increments `i`, and asserts that `i == 5`
 * at the end.
 */
void test_requires_ensures_loop()
{
  int i = 0;
  while(i < 5) 
  {
      int x = 0;
      int* ptr = &x;
      i = i + 1;
  }
  assert(i == 5);
}

/***
 * Description:
 * The `destroy` function simulates destroying an integer by assuming 
 * an invalid state.
 *
 * @param i - A pointer to an integer.
 */
void destroy(int* i) 
{
  // This function assumes an incorrect state.
}

/***
 * Description:
 * The `destroy_half` function simulates destroying half of an integer’s memory.
 *
 * @param i - A pointer to an integer.
 */
void destroy_half(int* i) 
{
  // This function assumes an incorrect state.
}

/***
 * Description:
 * The `break_statement` function demonstrates breaking out of a while loop.
 *
 * The function initializes `i` and iterates while `i < 1`, breaking after 
 * the first loop iteration.
 */
void break_statement()
{
  int i = 0;
  while(i < 1)
  {
    int x = 0;
    int* ptr = &x;    
    break;
  }
}
