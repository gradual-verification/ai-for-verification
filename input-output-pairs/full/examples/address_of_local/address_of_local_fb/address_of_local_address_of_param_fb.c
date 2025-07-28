

void inc(int* i)
  //@ requires *i |-> ?v;
  //@ ensures *i |-> v+1;
{
  (*i) = (*i) + 1;
}


// TODO: make this function pass the verification
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

