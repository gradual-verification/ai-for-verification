#include "stdio.h"

// TODO: make this function pass the verification
int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures true;
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv, argc, arguments);
    {
        //@ open argv(argv, argc, arguments);
        //@ assert 0 <= i &*& i < argc;
        //@ assert [_]pointer(argv + i, ?arg);
        //@ assert [_]string(arg, ?cs);
        puts(*(argv + i));
        //@ close argv(argv, argc, arguments);
    }
    return 0;
}