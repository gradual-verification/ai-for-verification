#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"
#include <stddef.h>
#include <limits.h>

/*@
  // Predicate to specify safe file structures
  predicate valid_file_pointer(struct file* f) = f != 0;

  // Predicate that guarantees allocated memory
  //predicate malloc_block(char* buffer, int size) = malloc_block(buffer, size);

  // Loop invariant
  //loop_invariant valid_file_pointer(from) &*& valid_file_pointer(to) &*& buffer != 0 &*&
  //               malloc_block(buffer, 100) &*& 0 <= nb_read &*& nb_read <= 100;
      
  // Memory safety after function call
  //ensures buffer != 0 &*& valid_file_pointer(from) &*& valid_file_pointer(to);

@*/
int main(int argc, char** argv)
//@ requires argc >= 0 &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  //@ open [_]argv(argv + 2, argc - 2, _);
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  nb_read = fread(buffer, 1, 100, from);
  
  while(0 < nb_read)
  /*@
    invariant file(from) &*& file(to) &*& buffer != 0 &*&
                   malloc_block(buffer, 100) &*& 0 <= nb_read &*& nb_read <= 100 &*&
                   buffer[..nb_read] |-> ?_ &*& buffer[nb_read..100] |-> _;
    @*/
  {
    int nb_written = fwrite(buffer, 1, (uintptr_t) nb_read, to);
    //@ chars_chars__join(buffer);
    nb_read = fread(buffer, 1, 100, from);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}
