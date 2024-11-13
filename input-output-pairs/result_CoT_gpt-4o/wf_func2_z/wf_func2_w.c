/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

predicate buffer(char *buf, int length, list<char> contents) =
    length >= 0 &*& chars(buf, length, contents);

predicate valid_index(char* buf, int index, int length) =
    0 <= index && index < length;

@*/

void fill(char *buf, int length, char c)
//@ requires buffer(buf, length, _);
//@ ensures buffer(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant valid_index(buf, i, length) &*& buffer(buf, length, _);
    {
        //@ open buffer(buf, length, _);
        buf[i] = c;
        //@ close buffer(buf, length, _);
    }
}

/*@
lemma void loop_invariant_preserved(char *buf, int i, int length, char c)
    requires valid_index(buf, i, length) &*& n_times(c, i);
    ensures valid_index(buf, i + 1, length) &*& n_times(c, i + 1);
{
    open n_times(c, i);
    close n_times(c, i + 1);
    open valid_index(buf, i, length);
    close valid_index(buf, i + 1, length);
}
@*/

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
