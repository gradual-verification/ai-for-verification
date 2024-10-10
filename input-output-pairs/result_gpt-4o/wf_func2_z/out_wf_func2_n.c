#include <stddef.h>

// Verifast annotations for ghost variables and predicate definitions

// Helper predicate that describes an array segment
predicate char_array(char *arr, int len;) =
  len == 0 ? emp : character(arr, _) &*& char_array(arr + 1, len - 1);

// Fill function specification and implementation
/**
 * Requires:
 * - `buf` points to a valid memory segment of at least `length` elements.
 * Ensures:
 * - All elements in the `buf` array from 0 to `length - 1` are set to `c`.
 * 
 * @requires length >= 0 && char_array(buf, length)
 * @ensures char_array(buf, length) &*& forall{i: int | 0 <= i && i < length}(buf[i] == c)
 */
void fill(char *buf, int length, char c)
    //@ requires length >= 0 &*& char_array(buf, length);
    //@ ensures char_array(buf, length) &*& forall(int i; 0 <= i && i < length)(buf[i] == c);
{
    for (int i = 0; i < length; i++)
        //@ invariant 0 <= i &*& i <= length &*& char_array(buf, length) &*& forall(int j; 0 <= j && j < i)(buf[j] == c);
    {
        buf[i] = c;
        //@ close char_array(buf + i, length - i - 1);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
