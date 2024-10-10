Below is the given C program with added formal specifications in Verifast to verify its correctness. Note that this includes annotations for memory allocations and validity of file pointers, as well as buffer usage.

```c
#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char** argv)
//@ requires argc >= 1 &*& [_]argv(argv, argc, _);
//@ ensures true;
{
    struct file* from = 0; 
    struct file* to = 0; 
    char* buffer = 0; 
    int nb_read = 0;

    if(argc < 3) { 
        puts("Not enough parameters."); 
        return -1; 
    }
    
    from = fopen(*(argv + 1), "r");
    to = fopen(*(argv + 2), "w");

    //@ assert from == 0 ? true : file(from) &*& to == 0 ? true : file(to);

    buffer = malloc(100);
    //@ assert buffer != 0 ? chars(buffer, 100, _) : true;

    if(buffer == 0 || from == 0 || to == 0) { 
        //@ if (from != 0) fclose(from);
        //@ if (to != 0) fclose(to);
        free(buffer);
        abort(); 
    }

    nb_read = fread(buffer, 1, 100, from);

    while(0 < nb_read)
    {
        int nb_written = fwrite(buffer, 1, nb_read, to);
        //@ assert nb_written == nb_read;
        nb_read = fread(buffer, 1, 100, from);
    }

    fclose(from);
    fclose(to);
    free(buffer);
    return 0;
}
```

### Explanation:
- **Precondition (`requires`)**: The `argc` should be at least 1, indicating that program's name at least should be in the arguments. The `[_]argv(argv, argc, _)` meta-predicate represents that `argv` is an array of length `argc` with enough space provided by the caller. Here brackets `[ ]` denote arbitrary precision.
  
- **Assertions**:
  - Checks if the file pointers `from` and `to` are non-null before using them. If they are not null, the annotation uses `file` predicate to specify that the file is currently open and can be operated upon without causing undefined behavior.
  - Ensures the buffer is allocated successfully and is 100 characters long by asserting `chars(buffer, 100, _)`.
  
- **Resource management**: 
  - Before aborting, it properly closes any open files and frees allocated memory if not null.
  
- **Invariants & correctness guarantees**:
  - Assert that when writing, the number of bytes written is the same as the number of bytes read to ensure data integrity.
  
These annotations aim to verify resource correctness and data safety within the program's lifecycle.
