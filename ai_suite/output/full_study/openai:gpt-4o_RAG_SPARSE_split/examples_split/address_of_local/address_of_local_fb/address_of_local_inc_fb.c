void inc(int* i)
  //@ requires integer(i, ?v);
  //@ ensures integer(i, v+1);
{
  //@ open integer(i, v);
  (*i) = (*i) + 1;
  //@ close integer(i, v+1);
}