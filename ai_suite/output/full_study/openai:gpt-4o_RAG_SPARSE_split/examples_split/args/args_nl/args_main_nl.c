#include "stdio.h"

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function prints each command-line argument to the standard output.
 *
 * @param argc - the number of command-line arguments.
 * @param argv - an array of strings containing the command-line arguments.
 * 
 */
int main(int argc, char **argv)
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures junk();
{
    for (int i = 0; i < argc; i++)
    //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv, argc, arguments);
    {
        puts(*(argv + i));
        //@ open argv(argv, argc, arguments);
        //@ close argv(argv, argc, arguments);
    }
    return 0;
}