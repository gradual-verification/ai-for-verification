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
    //@ open true;
    x = 5;
    int* ptr = &x; 
    //@ assert integer(ptr, 5);
    //@ produce_limits(x);
    inc(ptr);
    int z = x;
    assert(z == 6);
    //@ close true;
}
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
    //@ close integer(ptr, 5);
    //@ produce_limits(5);
    inc(ptr);
    int z = x;
    assert(z == 6);
    //@ open integer(ptr, 6);
}