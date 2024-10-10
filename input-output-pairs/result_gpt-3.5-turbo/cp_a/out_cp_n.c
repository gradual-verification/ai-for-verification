#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

/*@ 
predicate file(struct file* f; char* filename, char* mode, bool isOpen) =
  f != 0 &*&
  file_filename(f, filename) &*&
  file_mode(f, mode) &*&
  isOpen ?
    file_opened(f, _, _, _, _)
  :
    true;

predicate file_opened(struct file* f; FILE* file, char* filename, char* mode, int charactersWritten) =
  f != 0 &*&
  file == f &*&
  file_filename(f, filename) &*&
  file_mode(f, mode) &*&
  charactersWritten >= 0;

predicate file_filename(struct file* f; char* filename) = 
  f != 0 &*& filename != 0 &*&
  malloc_block(filename, strlen(filename) + 1) &*&
  f->filename |-> ?fn &*&
  chars(fn, filename, _);

predicate chars(char* ptr; list<char> chars, int size) =
  size == length(chars) &*&
  switch(chars)
  {
    case nil: return ptr == 0 &*& size == 0;
    case cons(h, t): return ptr != 0 &*& *ptr |-> h &*& chars(ptr + 1, t, size - 1);
  };

predicate file_mode(struct file* f; char* mode) = 
  f != 0 &*& mode != 0 &*& 
  malloc_block(mode, strlen(mode) + 1) &*&
  f->mode |-> ?mm &*&
  chars(mm, mode, _);

@*/

int main(int argc, char** argv)
  /*@ requires argc >= 3 &*& 
               pointer(&argc, _) &*& pointer(argv, _) &*&
               [_]c_char_array(argv, argc, ?args) &*& args[argc-1] == 0;
  @*/
  /*@ ensures pointer(&argc, _) &*& pointer(argv, _) &*& 
              [_]c_char_array(argv, argc, args); 
  @*/
{
  struct file* from = 0; 
  struct file* to = 0; 
  char* buffer = 0; 
  int nb_read = 0;
  if(argc < 3) 
  { 
    puts("Not enough parameters."); 
    return -1; 
  }
  
  from = fopen(* (argv + 1), "r");
  to = fopen(* (argv + 2), "w");
  buffer = malloc(100);
  if(buffer == 0 || from == 0 || to == 0) 
  { 
    abort(); 
  }
  
  nb_read = fread(buffer, 1, 100, from);
  while(0 < nb_read)
  /*@ invariant pointer(&argc, _) &*& pointer(argv, _) &*& 
                 [_]c_char_array(argv, argc, args) &*&
                 file(from, ?fromFName, "r", true) &*& file(to, ?toFName, "w", true) &*&
                 nb_read >= 0 &*& nb_read <= 100;
  @*/
  {
    int nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}
