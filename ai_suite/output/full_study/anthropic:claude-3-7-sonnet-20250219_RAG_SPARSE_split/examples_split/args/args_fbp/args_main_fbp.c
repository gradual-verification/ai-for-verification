#include "stdio.h"


int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    /*@
    // We need to prove that the array access is valid
    // For each iteration, we need to ensure that i is within bounds
    @*/
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv, argc, ?args);
    {
        puts(*(argv + i));
    }
    return 0;
}