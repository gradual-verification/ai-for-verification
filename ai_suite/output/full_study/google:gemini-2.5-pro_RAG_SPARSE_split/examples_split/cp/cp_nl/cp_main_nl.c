        /*@ invariant
              file(from) &*& file(to) &*&
              malloc_block(buffer, 100) &*&
              0 <= nb_read &*& nb_read <= 100 &*&
              chars(buffer, nb_read, ?cs_read) &*&
              chars_(buffer + nb_read, 100 - nb_read, _); @*/
#include "stdlib.h"
#include "stdio.h"


// TODO: make this function pass the verification
/*** 
 * Description:
The `main` function copies the content from a file to the other file (whose name are in command-line arguments).

@param `argc` - An integer representing the number of command-line arguments.
@param `argv` - An array of strings that are the command-line arguments.
*/
int main(int argc, char** argv) //@ : main
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) {
    puts("Not enough parameters.");
    return -1;
  }
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) {
    // In a real program, we should clean up here.
    // But for verification, abort() is enough as it has 'ensures false;'.
    // If from != 0, file(from) is leaked.
    // If to != 0, file(to) is leaked.
    // If buffer != 0, malloc_block(buffer, 100) and chars_(...) are leaked.
    if (from != 0) fclose(from);
    if (to != 0) fclose(to);
    if (buffer != 0) free(buffer);
    abort();
  }
  
  nb_read = fread(buffer, 1, 100, from);
  
  while(0 < nb_read)
    /*@
    invariant
      file(from) &*& file(to) &*&
      malloc_block(buffer, 100) &*&
      0 <= nb_read &*& nb_read <= 100 &*&
      chars(buffer, nb_read, ?cs_read) &*&
      chars_(buffer + nb_read, 100 - nb_read, _);
    @*/
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    
    //@ chars_to_chars_(buffer);
    //@ chars__join(buffer);
    
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  
  free(buffer);
  
  return 0;
}