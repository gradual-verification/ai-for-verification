enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires d >= monday && d <= sunday; // Specifies that the given day is within the bounds of valid days.
//@ ensures 0 <= result && result <= 6; // Ensures that the result is also within bounds of valid days.
//@ ensures d == sunday ? result == monday : result == d + 1; // Ensures that the function indeed returns the next day.
{
    if (d == sunday) {
        return monday;
    } else {
        //@ assert d != sunday;
        return d + 1;
    }
}

int main() //@ : main
//@ requires true; // There are no constraints for inputs for main.
//@ ensures true;  // No constraints on outputs.
{
    enum day d = monday;
    //@ assert d == monday; // Asserts that d starts with value of monday which is 0.
    
    d = 35; // This line should actually raise a warning because 35 is not a valid enum day.
    // Error: 35 is not a valid 'enum day'. Commenting this line would be prudent.
    // Assume we want to verify memory without considering this invalid assignment for now.
    
    int x = d;
    
    // Valid enum assertions
    assert(large_number == 30000);
    assert(another_large_number == 30001);
    assert(yaln + 1 == -0x7fff);
    return 0;
}
