// Declarations for Verifast
/*@
predicate buffer(char *buf, int length, list<char> cs) =
    length == 0 ?
        cs == nil :
        buf[0..length] |-> cs;
        
// Function Specification for `fill`
requires buffer(buf, length, ?cs) &*& 0 <= length;
ensures buffer(buf, length, ?fs) &*& length == length(fs);

// Fill function
*/
void fill(char *buf, int length, char c)
    //@ requires buffer(buf, length, ?contents) &*& 0 <= length;
    //@ ensures buffer(buf, length, ?new_contents) &*& length == length(new_contents);
{
    // Loop invariant
    /*@
    loop_invariant 0 <= i <= length &*& buffer(buf, length, ?xs) &*&
                   take(i, xs) == repeat(i, c) &*& length == length(xs);
    @*/
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i <= length &*& buffer(buf, length, ?cs);
    {
        buf[i] = c;
    }
}

int main()
{
    return 0;
}
