#include "stdlib.h"

static int global1 = -10;
static int global2 = 10;
static unsigned int global3 = 20; 
static char global4 = 'a';
static char global5 = 'b';

void modify_primitive_globals_old_syntax()
    /*@ 
        requires integer(&global1, ?val1) &*& integer(&global2, ?val2) &*&
            u_integer(&global3, ?val3) &*& character(&global4, ?val4) &*& character(&global5, ?val5);
    @*/
    /*@ 
        ensures integer(&global1, val1 + 5) &*& integer(&global2, val2 + 5) &*& 
            u_integer(&global3, val3 + 5) &*& character(&global4, (char)(val4 + 5)) &*& character(&global5, (char)(val5 + 5));
    @*/
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

void modify_primitive_globals_new_syntax()
    //@ requires global1 |-> ?val1 &*& global2 |-> ?val2 &*& global3 |-> ?val3 &*& global4 |-> ?val4 &*& global5 |-> ?val5;
    //@ ensures global1 |-> val1 + 5 &*& global2 |-> val2 + 5 &*& global3 |-> val3 + 5 &*& global4 |-> (char)(val4 + 5) &*& global5 |-> (char)(val5 + 5);
{
    global1 = global1 + 5;
    global2 = global2 + 5;
    global3 = global3 + 5;
    global4 = (char)(global4 + 5);
    global5 = (char)(global5 + 5);
}

int main() //@ : main_full(global_points_to_syntax_fb)
    //@ requires module(global_points_to_syntax_fb, true);
    //@ ensures true;
{
    modify_primitive_globals_old_syntax();
    modify_primitive_globals_new_syntax();

    return 0;
}


