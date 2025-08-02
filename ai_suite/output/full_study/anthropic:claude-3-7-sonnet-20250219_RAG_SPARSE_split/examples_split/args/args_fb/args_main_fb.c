#include "stdio.h"


int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    //@ open [_]argv(argv, argc, _);
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv + i, argc - i, _);
    {
        //@ open [_]argv(argv + i, argc - i, _);
        puts(*(argv + i));
        //@ close [_]argv(argv + i + 1, argc - i - 1, _);
    }
    return 0;
}