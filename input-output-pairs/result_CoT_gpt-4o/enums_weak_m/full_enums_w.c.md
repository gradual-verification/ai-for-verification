```c
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
```

The enumerations here are used to represent cyclic or periodical values, such as the days of the week, and large numbers where interesting constants are involved. Notice that in `main`, setting `d = 35` is illustrative and would not typically be allowed in a type-safe or verified code as it breaks the cycle bounds defined for `enum day`. 

The use of predicates serves to ensure certain conditions or expectations about the data are maintained, such as a valid range for `enum day`. The `next_day` function respects these conditions through correct arithmetic. The `assert` statements, while useful in verifying constant relationships, would typically be backed by more precise checks or assertions in real-world verified settings.
