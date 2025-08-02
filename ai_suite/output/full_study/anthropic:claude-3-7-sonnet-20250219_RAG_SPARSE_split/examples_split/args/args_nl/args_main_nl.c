#include "stdio.h"

//@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
//@ ensures true;
int main(int argc, char **argv)
{
    //@ open [_]argv(argv, argc, arguments);
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& [_]pointers(argv, argc, ?ps);
    {
        puts(*(argv + i));
    }
    return 0;
}