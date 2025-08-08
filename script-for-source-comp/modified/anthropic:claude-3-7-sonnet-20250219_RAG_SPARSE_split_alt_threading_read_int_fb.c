
struct thread;



int read_int()
{
    int *result = malloc(sizeof(int));
    if (result == 0) abort();
    *result = 0; // Initialize with a default value
    return result;
}
