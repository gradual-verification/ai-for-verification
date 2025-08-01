

// TODO: make this function pass the verification
void inc(int* i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v+1;
{
  (*i) = (*i) + 1;
}

