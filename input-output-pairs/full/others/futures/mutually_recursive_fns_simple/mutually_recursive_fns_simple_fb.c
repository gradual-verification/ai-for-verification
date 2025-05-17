/*@
fixpoint bool is_even(int x);
@*/

bool is_even_nat(int x)
//@ requires 0 <= x;
//@ ensures result == is_even(x);
{
  if(x == 0)
    return true;
  else if(x == 1)
    return false;
  else {
    return is_even_nat(x - 2);
  }
}