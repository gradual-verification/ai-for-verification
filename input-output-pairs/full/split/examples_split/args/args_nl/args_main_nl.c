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
{
    for (int i = 0; i < argc; i++)
    {
        puts(*(argv + i));
    }
    return 0;
}
