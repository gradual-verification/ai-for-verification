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
    //@ int old_x = x; // Save the initial value of x
    x = 5;
    int* ptr = &x; 
    //@ close exists<int>(x); // Existentially quantify the value of x
    inc(ptr);
    int z = x;
    assert(z == 6);
    //@ assert z == old_x + 1; // Ensure the final value of z is as expected
}