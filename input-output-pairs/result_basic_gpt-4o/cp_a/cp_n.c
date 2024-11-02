#include "stdlib.h"
#include "stdio.h"
#include "stdbool.h"
#include "assert.h"

/*@
  requires argc == 3;
  requires [_]is_cstring(argv[1]);
  requires [_]is_cstring(argv[2]);
  ensures result == 0 || result == -1;
  ensures (result == 0) ==> (file_exists(argv[1]) && file_exists(argv[2]));
  ensures (result == -1) ==> (!file_exists(argv[1]) || !file_exists(argv[2]));
@*/

int main(int argc, char** argv)
{
    struct file* from = 0; 
    struct file* to = 0; 
    char* buffer = 0; 
    int nb_read = 0;

    if(argc < 3) { puts("Not enough parameters."); return -1; }

    from = fopen(argv[1], "r");
    to = fopen(argv[2], "w");
    buffer = malloc(100);

    if(buffer == 0 || from == 0 || to == 0) { abort(); }

    /*@ loop_invariant buffer != 0 &*& from != 0 &*& to != 0; @*/
    while(0 < (nb_read = fread(buffer, 1, 100, from)))
    {
        int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
        //@ assert nb_written == nb_read;
    }

    fclose(from);
    fclose(to);
    free(buffer);

    return 0;
}
