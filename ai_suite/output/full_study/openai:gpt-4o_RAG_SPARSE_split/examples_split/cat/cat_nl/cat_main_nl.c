#include "stdio.h"
#include "stdlib.h"

//@ #include <list.gh>
//@ #include <stdio.gh>
//@ #include <stdlib.gh>

/*@
predicate main_io(place t1, list<list<char> > args, place t2) =
    args == cons(?filename, nil) &*&
    read_file_io(t1, filename, ?contents, ?t_read) &*&
    write_lines_io(t_read, contents, t2);
@*/

int main(int argc, char** argv) //@ : main_io
    //@ requires module(main, true) &*& [_]argv(argv, argc, ?arguments) &*& main_io(?t1, arguments, ?t2) &*& token(t1);
    //@ ensures token(t2);
{
    struct file* fp = 0;
    char* buffer = 0;
    char* res = 0;
    if(argc < 2) { fputs("Enter a file name.", stderr); return -1; }
    //@ open main_io(_, _, _);
    //@ open read_file_io(_, _, _, _);
    fp = fopen(argv[1], "r");
    buffer = malloc(sizeof(char) * 100);
    res = 0;
    if(fp == 0 || buffer == 0) { abort(); }
    //@ close write_lines_io(_, _, _);
    res = fgets(buffer, 100, fp);
    while(res != 0)
    {
        puts(buffer);
        res = fgets(buffer, 100, fp);
    }
    free((void *)buffer);
    fclose(fp);
    return 0;
}