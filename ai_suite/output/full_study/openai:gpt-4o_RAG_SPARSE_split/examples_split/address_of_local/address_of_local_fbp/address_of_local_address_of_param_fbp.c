void inc(int* i)
  //@ requires integer(i, ?v) &*& INT_MIN <= v &*& v < INT_MAX;
  //@ ensures integer(i, v+1);
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
    //@ close integer(ptr, x);
    inc(ptr);
    //@ open integer(ptr, _);
    int z = x;
    assert(z == 6);
}