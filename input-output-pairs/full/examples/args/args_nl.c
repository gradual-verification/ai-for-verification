#include "stdio.h"

/***
 * Description:
 * The `main` function prints each command-line argument to the standard output.
 *
 * @param argc - the number of command-line arguments.
 * @param argv - an array of strings containing the command-line arguments.
 *
 * The function iterates over the arguments and prints each one using `puts()`.
 */
int main(int argc, char **argv)
{
    for (int i = 0; i < argc; i++)
    {
        puts(*(argv + i));
    }
    return 0;
}
