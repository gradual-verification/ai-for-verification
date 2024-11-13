#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
predicate valid_file_pointer(struct file* f) = f != 0;
predicate valid_buffer(char* buffer, int size) = buffer != 0 &*& size == 100;
@*/

/**
 * Description:
 * The `main` function copies the content from a file to the other file.
 * It takes command-line arguments `argc` and `argv`.
 * It first opens the files to read from and write to, and uses a buffer as a bridge to continuously read and write.
 *
 * @param `argc` - An integer representing the number of command-line arguments.
 * @param `argv` - An array of strings that are the command-line arguments.
 */
/*@ 
  requires argc >= 3 &*& argv[0..argc] |-> ?args;
  ensures true;
@*/
int main(int argc, char** argv)
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;

  if(argc < 3) { puts("Not enough parameters."); return -1; }

  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");

  buffer = malloc(100);

  /*@
  open valid_buffer(buffer, 100);
  open valid_file_pointer(from);
  open valid_file_pointer(to);
  @*/
  if(buffer == 0 || from == 0 || to == 0) { abort(); }

  nb_read = fread(buffer, 1, 100, from);

  while(0 < nb_read)
  /*@
  invariant valid_buffer(buffer, 100) &*& valid_file_pointer(from) &*& valid_file_pointer(to);
  @*/
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t)nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }

  fclose(from);
  fclose(to);
  free(buffer);

  /*@
  close valid_buffer(buffer, 100);
  close valid_file_pointer(from);
  close valid_file_pointer(to);
  @*/
  return 0;
}
