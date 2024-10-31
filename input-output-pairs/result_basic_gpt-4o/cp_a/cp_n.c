#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

// Specification macros for VeriFast
/*@
predicate file_pointer(FILE* f) = \valid(f);

predicate buffer_allocated(char* buffer, int size) = 
  \valid(buffer + (0 .. size-1)) && size == 100;

predicate files_closed = true;
@*/

/***
 * Description:
 * The `main` function copies the content from a file to the other file. 
 * It takes command-line arguments `argc` and `argv`.
 * It first opens the files to read from and write to, and uses a buffer as a 
 * bridge to continuously read and write.
 *
 * @param `argc` - An integer representing the number of command-line arguments.
 * @param `argv` - An array of strings that are the command-line arguments.
 */
/*@
requires argc > 0 && \valid(argv + (0 .. argc-1)) && \forall int i; (0 <= i < argc ==> \valid(argv[i]));
ensures files_closed;
@*/
int main(int argc, char** argv)
{
  FILE* from = 0;
  FILE* to = 0;
  char* buffer = 0;
  int nb_read = 0;

  if(argc < 3) {
    puts("Not enough parameters.");
    //@ ensures files_closed;
    return -1; 
  }

  from = fopen(argv[1], "r");
  //@ assert file_pointer(from);
  to = fopen(argv[2], "w");
  //@ assert file_pointer(to);

  buffer = malloc(100);
  //@ open buffer_allocated(buffer, 100);
  
  if(buffer == 0 || from == 0 || to == 0) {
    abort(); 
  }
  
  nb_read = fread(buffer, 1, 100, from);

  /*@ 
  loop invariant 0 <= nb_read <= 100;
  loop invariant \valid(buffer + (0 .. 99));
  loop assigns nb_read, buffer[0 .. nb_read-1];
  @*/
  while(0 < nb_read)
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }

  fclose(from);
  fclose(to);
  free(buffer);

  //@ ensures files_closed; 
  return 0;
}
