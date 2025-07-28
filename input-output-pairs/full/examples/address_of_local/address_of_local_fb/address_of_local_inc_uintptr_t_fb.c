

// TODO: make this function pass the verification
void inc_uintptr_t(uintptr_t *i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v + 1;
{
  (*i) = (*i) + 1;
}

