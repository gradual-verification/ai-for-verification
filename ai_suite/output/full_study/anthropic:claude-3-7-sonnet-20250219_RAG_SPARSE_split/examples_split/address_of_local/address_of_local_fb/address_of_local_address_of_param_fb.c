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
    //@ open true;
    x = 5;
    //@ close x |-> 5;
    int* ptr = &x; 
    //@ assert *ptr |-> 5;
    inc(ptr);
    //@ assert *ptr |-> 6;
    int z = x;
    //@ assert z == 6;
    assert(z == 6);
    //@ close true;
}