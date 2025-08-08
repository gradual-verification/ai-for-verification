
int read_int()
{
    int x;
    int result = scanf("%i", &x);
    if (result < 1) abort();
    return x;
}
