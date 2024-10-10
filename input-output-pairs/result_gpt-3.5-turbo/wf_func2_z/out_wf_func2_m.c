struct node {
    struct node *next;
};

/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires buf[0..length] |-> _;
//@ ensures buf[0..length] |-> n_times(c, length);
{
    for (int i = 0; i < length; i++)
    /*@
    loop invariant 0 <= i <= length;
    loop assigns i, buf[0..length];
    loop variant length - i;
    */
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
