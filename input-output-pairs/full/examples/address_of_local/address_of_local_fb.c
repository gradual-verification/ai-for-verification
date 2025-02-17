#include <stdint.h>
#include <stdbool.h>

void inc(int* i)
  //@ requires integer(i, ?v);
  //@ ensures integer(i, v+1);
{
  (*i) = (*i) + 1;
}

void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}

void address_of_param(int x) 
  //@ requires true;
  //@ ensures true;
{
    x = 5;
    int* ptr = &x; 
    inc(ptr);
    int z = x;
    assert(z == 6);
}

void address_of_local() 
  //@ requires true;
  //@ ensures true;
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

void address_of_local_uintptr_t() 
  //@ requires true;
  //@ ensures true;
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

void test_goto() 
  //@ requires true;
  //@ ensures true;
{
  goto end;
  {
    int x = 5;
    int *p = &x; 
    abort(); 
  }
  end:
}

void test_goto2()
  //@ requires true;
  //@ ensures true;
{
  {
    int x = 0;
    int* ptr = &x;
    goto end;
  }
  end:
}

void test_goto3()
  //@ requires true;
  //@ ensures true;
{
  {
    int x = 0;
    int* ptr = &x;
    goto next;
    next:
    x = 3;
  }
}

void test_break()
  //@ requires true;
  //@ ensures true;
{
  while(true) 

  {
    int x = 0;
    int* ptr = &x;
    break;
  }
}

void test_break2()
  //@ requires true;
  //@ ensures true;
{
  while(true) 
    //@ requires true;
    //@ ensures true;
  {
      int x = 0;
      int* ptr = &x;
      break;
  }
}

void test_requires_ensures_loop()
  //@ requires true;
  //@ ensures true;
{
  int i = 0;
  while(i < 5) 
    //@ requires i <= 5;
    //@ ensures i <= 5;
  {
      int x = 0;
      int* ptr = &x;
      i = i + 1;
  }

}

void destroy(int* i) 
  //@ requires integer(i, _);
  //@ ensures true;
{
 
}


void destroy_half(int* i) 
  //@ requires [1/2]integer(i, _);
  //@ ensures true;
{

}

void break_statement()
  //@ requires true;
  //@ ensures true;
{
  int i = 0;
  while(i < 1)
 
  {
    int x = 0;
    int* ptr = &x;    
    break;
  }
}



