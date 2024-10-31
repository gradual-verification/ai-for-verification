#include <assert.h>

enum day
{
  monday = 0,
  tuesday,
  wednesday,
  thursday,
  friday,
  saturday,
  sunday
};

enum large_numbers
{
  large_number = 30000,
  another_large_number, // This will be 30001
  yaln = -0x7fff - 1    // Compute this to be -32768
};

/*@
  requires 0 <= d <= 6;
  ensures 0 <= \result <= 6;
@*/
enum day next_day(enum day d)
{
  //@ assert 0 <= d <= 6;

  int sum = d + 1;
  //@ assert 1 <= sum <= 7;

  int r = sum % 7;
  //@ assert 0 <= r <= 6;

  return r;
}

/*@
  lemma void compute_large_numbers()
    requires true;
    ensures large_number == 30000 &*& another_large_number == 30001 &*& yaln == -32768 &*& yaln + 1 == -32767;
  {
    // VeriFast computes constants, but we can help it along
    // Compute another_large_number
    assert(another_large_number == large_number + 1);
    assert(another_large_number == 30001);
    // Compute yaln
    assert(yaln == (-0x7fff) - 1);
    assert(yaln == (-32767) - 1);
    assert(yaln == -32768);
    assert(yaln + 1 == -32767);
  }
@*/

/*@
  requires true;
  ensures true;
@*/
int main()
{
  enum day d = monday;

  d = 35;  // Assigning an integer to an enum variable is acceptable in C

  int x = d;

  //@ compute_large_numbers();

  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff); // -0x7fff equals -32767

  return 0;
}
