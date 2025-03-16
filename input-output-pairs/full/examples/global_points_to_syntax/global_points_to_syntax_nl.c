#include "stdlib.h"

static int global1 = -10;
static int global2 = 10;
static unsigned int global3 = 20; 
static char global4 = 'a';
static char global5 = 'b';

/*** 
 * Description:
The modify_primitive_globals_old_syntax function increments the value of a global variables
(global1, global2, global3, global4 and global5) by 5.

Here, old syntax means we can use "integer(int *p; int v)" to show that an p points to an integer with value v.
*/
void modify_primitive_globals_old_syntax()
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

/*** 
 * Description:
The modify_primitive_globals_new_syntax function increments the value of a global variables
(global1, global2, global3, global4 and global5) by 5.

Here, new syntax means we can use "p |-> v" to show that variable p has value v.
*/
void modify_primitive_globals_new_syntax()
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

/***
 * Description:
The main function calls two functions to increment the value of global variables.
*/
int main() //@ : main_full(global_points_to_syntax_nl)
{
    modify_primitive_globals_old_syntax();
    modify_primitive_globals_new_syntax();

    return 0;
}


