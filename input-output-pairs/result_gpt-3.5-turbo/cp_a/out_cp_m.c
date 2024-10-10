#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, ?values) &*& values[argc] == '\0';
//@ ensures true;
{
  struct file* from = 0; struct file* to = 0; char* buffer = 0; int nb_read = 0;
  
  if(argc < 3) { puts("Not enough parameters."); return -1; }
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100 * sizeof(char));
  
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  
  nb_read = fread(buffer, sizeof(char), 100, from);
  while(0 < nb_read)
    //@ invariant 0 <= nb_read &*& buffer[0..nb_read] |-> _ &*& from |-> _ &*& to |-> _;
  {
    int nb_written = fwrite(buffer, sizeof(char), nb_read, to);
    nb_read = fread(buffer, sizeof(char), 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);

  return 0;
}
