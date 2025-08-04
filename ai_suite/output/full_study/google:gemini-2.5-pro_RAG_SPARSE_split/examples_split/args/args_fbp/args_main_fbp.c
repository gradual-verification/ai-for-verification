#include "stdio.h"


// TODO: make this function pass the verification
int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?args);
    //@ ensures true;
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv + i, argc - i, drop(i, args));
    {
        //@ open [_]argv(argv + i, argc - i, drop(i, args));
        puts(*(argv + i));
    }
    return 0;
}