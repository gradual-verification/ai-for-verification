typedef int my_int;

// Predicate and functions declarations
//@ predicate my_int_valid(my_int x) = x >= INT_MIN && x <= INT_MAX;

int main()
//@ requires true;
//@ ensures true;
{
    my_int x = 5;
    //@ close my_int_valid(x);
    
    int y = x;
    //@ assert my_int_valid(x);  // Ensure x is a valid my_int
    
    my_int z = 3;
    //@ close my_int_valid(z);
    
    my_int t = x + z;
    //@ assert my_int_valid(t);  // Ensure t is a valid my_int

    assert(t == 8);
    
    //@ leak my_int_valid(x);  // Leak memory predicate x
    //@ leak my_int_valid(z);  // Leak memory predicate z
    //@ leak my_int_valid(t);  // Leak memory predicate t
    
    return 0;
}
