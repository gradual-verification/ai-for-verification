// Declarations for Verifast
/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

/*@
predicate buffer(char *buf, int length, list<char> cs) =
    length == 0 ?
        cs == nil :
        buf[0..length] |-> cs;
        
// Function Specification for `fill`
//requires buffer(buf, length, ?cs) &*& 0 <= length;
//ensures buffer(buf, length, ?fs) &*& length == length(fs);

// Fill function
@*/
void fill(char *buf, int length, char c)
    //@ requires buffer(buf, length, ?contents) &*& 0 <= length;
    //@ ensures buffer(buf, length, ?new_contents) &*& length == length(new_contents);
{
    // Loop invariant
    /* @
    loop_invariant 0 <= i <= length &*& buffer(buf, length, ?xs) &*&
                   take(i, xs) == repeat(i, c) &*& length == length(xs);
    @*/
    //@ open buffer(buf, length, _);
    for (int i = 0; i < length; i++)
    //@ requires 0 <= i &*& i <= length &*& chars_(buf + i, length - i, ?cs);
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        buf[i] = c;
    }
    //@ close buffer(buf, length, _);
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
