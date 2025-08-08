


void invert(int *A, int N, int *B)
{
    for (int i = 0; i < N; i++)
    {
        int ai = *(A + i);
        
        
        *(B + ai) = i;
        
    }
    
}
