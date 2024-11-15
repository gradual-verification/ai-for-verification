#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

// Predicate for array ownership
predicate array(char* arr, int length) = chars(arr, length, _);

// Predicate to ensure argv is a valid array of strings
predicate argv(char** argv, int argc, list<char*> arglist) = true;

int main(int argc, char** argv) 
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
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
    //@ close array(buffer, 100);

    res = 0;
    if(fp == 0 || buffer == 0) { 
        free(buffer);
        abort(); 
    }
    
    res = fgets(buffer, 100, fp);
    while(res != 0) 
    //@ invariant array(buffer, 100) &*& res != 0;
    {
        puts(buffer);
        res = fgets(buffer, 100, fp);
    }
    
    //@ open array(buffer, 100);
    free(buffer);
    fclose(fp);
    return 0;
}
