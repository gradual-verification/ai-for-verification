#include "stdio.h"


// TODO: make this function pass the verification
int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    for (int i = 0; i < argc; i++)
    {
        puts(*(argv + i));
    }
    return 0;
}
