#include "stdio.h"
#include "stdlib.h"

//@ #include "nat.gh"

// VeriFast annotations include:
// `requires` that specifies the preconditions
// `ensures` that specifies the postconditions

int main(int argc, char** argv) //@ : main
//@ requires argc >= 2 &*& argv(argv, argc, _); // Partial knowledge about argv
//@ ensures true;
{
    FILE* fp = NULL; 
    char* buffer = NULL; 
    char* res = NULL;

    if (argc < 2) { 
        puts("Enter a file name."); 
        return -1; 
    }
    
    fp = fopen(argv[1], "r");
    buffer = malloc(sizeof(char) * 100);
    res = NULL;

    if (fp == NULL || buffer == NULL) { 
        if (buffer != NULL) free(buffer);
        if (fp != NULL) fclose(fp);
        abort(); 
    }
    
    //@ close exists<int>(100);
    res = fgets(buffer, 100, fp);

    while (res != NULL) 
    //@ invariant buffer != NULL;
    {
        puts(buffer);
        res = fgets(buffer, 100, fp);
    }

    free(buffer);
    fclose(fp);
    
    return 0;
}
