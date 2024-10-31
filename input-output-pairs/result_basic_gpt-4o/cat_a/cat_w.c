#include "stdio.h"
#include "stdlib.h"

// Verifast will need specific header files for handling the pointers as predicates
#include "vfstdlib.h"

int main(int argc, char** argv) //@ : main
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
    
    fp = fopen(*(argv + 1), "r");
    buffer = malloc(sizeof(char) * 100);
    
    if(fp == 0 || buffer == 0) {
        if (buffer != 0) free(buffer);
        if (fp != 0) fclose(fp);
        abort();
    }
    
    //@ close chars(buffer, 100, _);
    
    res = fgets(buffer, 100, fp);
    while(res != 0) 
    {
        puts(buffer);
        //@ close chars(res, 100, _);
        res = fgets(buffer, 100, fp);
    }
    
    //@ open chars(buffer, 100, _);
    free(buffer);
    fclose(fp);
    
    return 0;
}
