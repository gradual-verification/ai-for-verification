#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@
  predicate file_opened(struct file* f) =
    f != 0;

  predicate buffer_allocated(char* buffer, int size) =
    buffer != 0 &*& malloc_block(buffer, size);

  predicate file_copying_status(struct file* from, struct file* to, char* buffer) =
    file_opened(from) &*& file_opened(to) &*& buffer_allocated(buffer, 100);

  predicate main_preconditions(int argc, char** argv) =
    argc >= 3 &*& argv != 0 &*& 
    [_]strings(argv, argc, ?argv_strings) &*&
    length(argv_strings) == argc;

  predicate main_postconditions() = true;

  lemma void strings(void** strings, int count, list<cs> strs);

@*/

int main(int argc, char** argv) 
//@ requires main_preconditions(argc, argv);
//@ ensures main_postconditions();
{
  struct file* from = 0; 
  struct file* to = 0; 
  char* buffer = 0; 
  int nb_read = 0;

  if (argc < 3) { 
    puts("Not enough parameters."); 
    return -1; 
  }

  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);

  /*@ 
    if (buffer == 0 || from == 0 || to == 0) {
      free(buffer); 
      if (from != 0) fclose(from); 
      if (to != 0) fclose(to);
      abort();
    } 
  @*/

  if (buffer == 0 || from == 0 || to == 0) { abort(); }

  //@ close file_copying_status(from, to, buffer);

  nb_read = fread(buffer, 1, 100, from);
  while (0 < nb_read)
  //@ invariant file_copying_status(from, to, buffer);
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }

  fclose(from);
  fclose(to);
  free(buffer);

  return 0;
}
