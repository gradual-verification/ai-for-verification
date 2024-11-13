#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

// Define a predicate for the argv argument
//@ predicate argv(char** arr, int count, list<char*> strings) = count == 0 ? strings == nil : [1/2]arr[0] |-> ?first &*& [1/2]string(first, _) &*& argv(arr + 1, count - 1, ?rest) &*& strings == cons(first, rest);

int main(int argc, char** argv) //@ : main
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
    res = 0;

    if(fp == 0 || buffer == 0) {
        abort();
    }
    
    res = fgets(buffer, 100, fp);
    //@ open [1/2]malloc_block(buffer, 100);
    
    while(res != 0) 
    //@ invariant [1/2]malloc_block(buffer, 100);
    {
        puts(buffer);
        res = fgets(buffer, 100, fp);
    }
    
    //@ close [1/2]malloc_block(buffer, 100);
    free(buffer);
    fclose(fp);
    
    return 0;
}
