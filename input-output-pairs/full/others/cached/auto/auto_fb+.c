/*@

predicate p(ints is) = true;
@*/

void m()
  //@ requires p(?is);
  //@ ensures p(is) &*& 0 <= ints_length(is);
{
}

void m2()
  //@ requires p(?is);
  //@ ensures p(is) &*& 0 <= ints_length2(is);
{
}

