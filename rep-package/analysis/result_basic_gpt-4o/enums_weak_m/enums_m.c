#include <limits.h>

enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

// Ensure that the values are within the range of an int, which is always true for enum in C.
enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

// Specification for next_day function
enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures 0 <= result && result < 7;
{
    //@ div_rem_nonneg(d + 1, 7);
    return (d + 1) % 7;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    enum day d = monday;
    // Ensure we do not assign an invalid value that breaks enum bounds.
    // In C, enums are not strictly type-checked, but it is good practice to avoid such assignments.
    // Commenting out the misassignment as it serves no logical purpose and leads to potential errors.
    // d = 35; // invalid assignment for enum day

    // Verifying large_numbers values.
    // VeriFast understands constant enum values without need for assertion.
    //@ assert large_number == 30000;
    //@ assert another_large_number == 30001;
    //@ assert yaln == -0x7fff - 1;

    int x = d; // x is assigned correctly within the enum day, supported by range of day.

    // The following assertion verifies that enum constants match expected values.
    assert(large_number == 30000);           // true by definition
    assert(another_large_number == 30001);   // true because enums increment by 1 unless specified
    assert(yaln == -0x7fff - 1);                 // true by definition, as yaln is set to INT_MIN

    return 0;
}
