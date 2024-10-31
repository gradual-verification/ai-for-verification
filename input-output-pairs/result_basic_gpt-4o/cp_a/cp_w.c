#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

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
    
    from = fopen(argv[1], "r");
    to = fopen(argv[2], "w");
    buffer = malloc(100);
    
    if(buffer == 0 || from == 0 || to == 0) { 
        abort(); 
    }
    
    //@ assert buffer != 0;
    //@ assert from != 0;
    //@ assert to != 0;
    
    nb_read = fread(buffer, 1, 100, from);
    
    while(0 < nb_read)
    //@ invariant buffer != 0 &*& from != 0 &*& to != 0;
    {
        int nb_written = fwrite(buffer, 1, nb_read, to);
        //@ assert nb_written == nb_read; // Check that all bytes read are written
        nb_read = fread(buffer, 1, 100, from);
    }
    
    fclose(from);
    fclose(to);
    free(buffer);
    
    return 0;
}
