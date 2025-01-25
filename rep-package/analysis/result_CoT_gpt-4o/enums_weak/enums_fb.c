enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;  // The input day is within valid bounds (enum day range).
//@ ensures 0 <= result && result < 7;  // Resulting day is also within valid bounds (enum day range).
{
    //@ div_rem_nonneg(d + 1, 7);
    return (d + 1) % 7;  // Logic to get the next day in the week.
}

int main() //@ : main
//@ requires true;  // No preconditions, as this is the entry point for the program.
//@ ensures true;  // No postcondition other than termination assurance.
{
    enum day d = monday;
    d = 35;  // This assignment goes against our safe bound assumption on 'd', it's illustrative for verification.
    int x = d;

    // Ensure the static assertions hold
    assert(large_number == 30000);  // Asserting the constant value for large_number.
    assert(another_large_number == 30001);  // Slight increment check on the previous large number.
    assert(yaln + 1 == -0x7fff);  // Border case for negative max range establishment.
    
    return 0;
}
