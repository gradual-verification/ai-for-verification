#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char** argv) 
//@ requires [_]argv(argv, argc, _);
//@ ensures true;
{
  struct file* from = 0;
  struct file* to = 0;
  char* buffer = 0;
  int nb_read = 0;

  if(argc < 3) {
    puts("Not enough parameters.");
    return -1;
  }

  from = fopen(argv[1], "r");
  if(from == 0) {
    abort();
  }

  to = fopen(argv[2], "w");
  if(to == 0) {
    fclose(from);
    abort();
  }

  buffer = malloc(100);
  if(buffer == 0) {
    fclose(from);
    fclose(to);
    abort();
  }

  nb_read = fread(buffer, 1, 100, from);
  //@ loop_invariant 0 <= nb_read <= 100;
  //@ loop_invariant from != 0 &*& to != 0 &*& buffer[0..100] |-> ?cs;
  //@ loop_invariant is_real_int(env(numeric), nb_read, true, none);
  while(0 < nb_read)
  /*@ invariant from != 0 &*& to != 0 &*& malloc_block(buffer, 100);
      @*/
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    //@ assert(nb_written == nb_read); // Assuming fwrite writes all data
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);
  
  return 0;
}
