#include "stdio.h"
#include <stdbool.h>

/***
 * Function: read_int
 *
 * Description:
 * Repeatedly prompts the user until a valid integer is entered.
 * If `scanf` fails to read an integer (returns 0), the user is prompted again.
 * If an end-of-file (EOF) condition is encountered, the program aborts.
 *
@return The integer value entered by the user.
 */
int read_int()
{
    int value = 0;
    while (true)
    {
        int result = scanf("%d\n", &value);
        if (result == EOF) abort();
        if (result == 1) break;
        puts("Please enter a number.");
    }
    return value;
}

/***
 * Function: read_string
 *
 * Description:
 * Reads a string from standard input, with a buffer limit of 40 characters.
 * Removes the newline character at the end of the input, if present.
 * Aborts the program if the input fails (e.g., EOF).
 *
@return A pointer to the dynamically allocated null-terminated string.
 */
char *read_string()
{
    int n;
    char *buffer = malloc(40);
    char *result = fgets(buffer, 40, stdin);
    if (result == 0) abort();
    n = strlen(buffer);
    if (n > 0 && buffer[n - 1] == '\n')
        buffer[n - 1] = 0;
    return buffer;
}
