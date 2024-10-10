```c CODE and SPEC
/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> n_times(c, length);
{
    for (int i = 0; i < length; i++)
    //@ requires buf[..length] |-> ?contents &*& length >= i &*& i >= 0;
    //@ ensures buf[..length] |-> n_times(c, length);
    {
        buf[i] = c;
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
```
