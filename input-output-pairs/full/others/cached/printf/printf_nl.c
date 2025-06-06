#include <math.h>
#include "stdio.h"

/***
 * Function: main
 *
 * Description:
 * - Declares a simple message string.
 * - Uses `printf` multiple times to demonstrate:
 *   - Basic string printing
 *   - Variable substitution
 *   - Integer division and remainder
 *   - Advanced format flags (e.g., width, precision, alignment, sign, zero-padding)
 *   - Long and unsigned integer types
 *
@return 0 on successful execution.
 */
int main()
{
    char msg[10] = "Hi there!";
    
    printf("Hello, world!\n");
    printf("Hello, %s!\n", "world!");
    printf("%s\n", msg);
    printf("%d divided by %d is %d with remainder %d.\n", 10, 3, 10 / 3, 10 % 3);
    printf("%-+#0*.*e % 3.4f %55.66g %s %s", 33, 44, 1.0, 2.0, 3.0, "Hi", "there");
    printf("%ld %lld %lu %llu\n", (long)42, (long long)42, (unsigned long)42, (unsigned long long)42);
    return 0;
}
