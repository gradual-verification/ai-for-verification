enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

// Define predicates for memory regions or structures if needed
//@ predicate valid_day(enum day d) = 0 <= d && d < 7;

enum day next_day(enum day d)
    //@ requires valid_day(d);
    //@ ensures valid_day(result);
{
    // Implementing the cyclic behavior of days in a week
    return (d + 1) % 7;
}

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

int main() 
    //@ requires true;
    //@ ensures true;
{
    enum day d = monday;
    // Ensuring value is within enumeration range
    //@ assert valid_day(d);

    // Assigning an out-of-range value is unsafe. The assignment is only for demonstrative purposes and would be flagged in real use.
    d = 35; 
    
    //@ assert !valid_day(d); // Out of range assert for demonstration
    
    int x = d; // Converting enum to int, safe as enums can be treated as integers within their range.
    
    // Verifying defined constant values
    assert(large_number == 30000);
    assert(another_large_number == 30001);
    
    // Integer overflow/underflow verification
    assert(yaln + 1 == -0x7fff);
    
    return 0;
}
