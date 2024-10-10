#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

struct file; // Forward declaration to let Verifast know that we will define a 'file' struct later

//@ predicate file(FILE* fp) = fp != 0 &*& file_struct_fields(fp, _);

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _) &*& malloc_block_file(?fp) &*& chars(argv, argc, _) &*& argv[argc] == 0;
//@ ensures true;
{
    struct file* fp = 0; char* buffer = 0; char* res = 0;
    if(argc < 2) { puts("Enter a file name."); return -1; }
    fp = fopen(argv[1], "r");
    buffer = malloc(sizeof(char) * 100);
    res = 0;
    if(fp == 0 || buffer == 0) { abort(); }
    res = fgets(buffer, 100, fp);
    while(res != 0) 
    {
        puts(buffer);
        res = fgets(buffer, 100, fp);
    }
    free(buffer);
    fclose(fp);
    return 0;
}
