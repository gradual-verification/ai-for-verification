
struct thread;



int read_int()
{
    int *value = malloc(sizeof(int));
    if (value == 0) abort();
    *value = 0; // Initialize with a default value
    
    int result = *value;
    free(value);
    
    return result;
}
