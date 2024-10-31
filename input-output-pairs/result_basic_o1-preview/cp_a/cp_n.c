#include "stdlib.h"
#include "stdio.h"

/*@
predicate file(FILE* f);

predicate malloc_block(void* p; int size);

predicate chars(char *p; list<char> cs);

FILE* fopen(char* filename, char* mode);
  //@ requires [?f1]chars(filename, ?fname) &*& [?f2]chars(mode, ?m);
  //@ ensures result == 0 ? true : file(result);

int fclose(FILE* f);
  //@ requires file(f);
  //@ ensures true;

size_t fread(void *ptr, size_t size, size_t nmemb, FILE *stream);
  //@ requires malloc_block(ptr, size * nmemb) &*& file(stream);
  //@ ensures malloc_block(ptr, size * nmemb) &*& file(stream) &*& 0 <= result &*& result <= nmemb;

size_t fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream);
  //@ requires malloc_block(ptr, size * nmemb) &*& file(stream);
  //@ ensures malloc_block(ptr, size * nmemb) &*& file(stream) &*& 0 <= result &*& result <= nmemb;

void* malloc(size_t size);
  //@ requires 0 <= size;
  //@ ensures result == 0 ? true : malloc_block(result, size);

void free(void* p);
  //@ requires malloc_block(p, _);
  //@ ensures true;

int main(int argc, char** argv)
  //@ requires argc >= 3 &*& [_]chars(argv[1], _) &*& [_]chars(argv[2], _);
  //@ ensures true;
{
  FILE* from = 0; 
  FILE* to = 0; 
  char* buffer = 0; 
  size_t nb_read = 0;
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  
  if(buffer == 0 || from == 0 || to == 0) {
    if (buffer != 0) { free(buffer); }
    if (from != 0) { fclose(from); }
    if (to != 0) { fclose(to); }
    return -1;
  }
  
  nb_read = fread(buffer, 1, 100, from);
  //@ loop_invariant malloc_block(buffer, 100) &*& file(from) &*& file(to);
  while(0 < nb_read)
  {
    size_t nb_written = fwrite(buffer, 1, nb_read, to);
    nb_read = fread(buffer, 1, 100, from);
  }
  
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}
