#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

//@ predicate file(struct file* f; char* filename, char* mode; int descriptor);

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, ?args) &*& chars(args, argc, ?charsArgs) &*& pointer(argv, argc, charsArgs);
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  from = fopen(* (argv + 1), "r");
  to = fopen(* (argv + 2), "w");
  buffer = malloc(100);
  
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  
  nb_read = fread(buffer, 1, 100, from);
  
  while(0 < nb_read)
  //@ invariant file(from, ?fromName, "r", _) &*& file(to, ?toName, "w", _) &*& characters(buffer, 100, _);
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);
  
  return 0;
}
