

void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> n_times(c, length);
{
    for (int i = 0; i < length; i++)
    {
        buf[i] = c;
    }
}
