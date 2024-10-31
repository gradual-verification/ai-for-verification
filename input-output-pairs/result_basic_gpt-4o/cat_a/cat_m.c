#include "stdio.h"
#include "stdlib.h"

int main(int argc, char** argv)
//@ requires argc > 0 &*& [_]argv(argv, argc, _);
//@ ensures true;
{
    struct file* fp = 0; 
    char* buffer = 0; 
    char* res = 0;

    if(argc < 2) { 
        puts("Enter a file name."); 
        return -1; 
    }

    //@ open argv(argv, argc, _);
    fp = fopen(*(argv + 1), "r");
    buffer = malloc(sizeof(char) * 100);
    res = 0;
    
    if(fp == 0 || buffer == 0) { 
        if(buffer != 0) free(buffer); 
        puts("Error during file opening or memory allocation.");
        if(fp != 0) fclose(fp);
        return -1; 
    }
    
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
