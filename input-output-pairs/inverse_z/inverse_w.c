// VSTTE 2010 Competition Problem 2. Problem statement by P. Mueller and N. Shankar.

//@ #include "nat.gh"
//@ #include "listex.gh"




void invert(int *A, int N, int *B)
    //@ requires ints(A, N, ?as) &*& ints(B, N, _);
    //@ ensures ints(A, N, as) &*& ints(B, N, ?bs);
{
    for (int i = 0; i < N; i++)
    {
        int ai = *(A + i);
        *(B + ai) = i;
    }
}
