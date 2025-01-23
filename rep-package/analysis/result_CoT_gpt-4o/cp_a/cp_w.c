#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

//struct file;

// Function contracts for fopen, fread, fwrite, fclose, malloc, free are assumed to be predefined

int main(int argc, char** argv) //@ : main
//@ requires argc >= 0 &*& [_]argv(argv, argc, _);
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
    //@ open [_]argv(argv, argc, _);
    //@ open [_]argv(argv + 1, argc - 1, _);
    //@ open [_]argv(argv + 2, argc - 2, _);
    from = fopen(argv[1], "r");
    to = fopen(argv[2], "w");
    buffer = malloc(100);
    
    if(buffer == 0 || from == 0 || to == 0) {
        abort();
    }

    //@ assert buffer[..100] |-> _ &*& file(from) &*& file(to);

    nb_read = fread(buffer, 1, 100, from);

    while(0 < nb_read)
    //@ invariant buffer[..nb_read] |-> ?_ &*& nb_read <= 100 &*& buffer[nb_read..100] |-> _ &*& file(from) &*& file(to);
    {
        int nb_written = fwrite(buffer, 1, (uintptr_t) nb_read, to);
        //@ chars_chars__join(buffer);
        nb_read = fread(buffer, 1, 100, from);
    }

    fclose(from);
    fclose(to);
    free(buffer);

    // @ assert zero_length(buffer);
    return 0;
}
