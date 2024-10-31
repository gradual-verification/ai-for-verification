#include "stdlib.h"
#include "stdio.h"
#include <stdbool.h>
#include "assert.h"

// File handling

struct file;
predicate file(struct file *f;);

struct file* fopen(char* filename, char* mode);
  //@ requires [?fn]string(filename, ?fname) &*& [?fm]string(mode, ?modes);
  //@ ensures result == 0 ? [fn]string(filename, fname) &*& [fm]string(mode, modes) : [fn]string(filename, fname) &*& [fm]string(mode, modes) &*& file(result);

int fclose(struct file* f);
  //@ requires file(f);
  //@ ensures true;

size_t fread(void *ptr, size_t size, size_t nmemb, struct file *stream);
  //@ requires file(stream) &*& chars(ptr, size * nmemb, _);
  //@ ensures file(stream) &*& chars(ptr, size * nmemb, ?cs_read) &*& result <= nmemb;

size_t fwrite(const void *ptr, size_t size, size_t nmemb, struct file *stream);
  //@ requires file(stream) &*& [?f]chars((void*)ptr, size * nmemb, ?cs) &*& f == 1.0;
  //@ ensures file(stream) &*& [f]chars((void*)ptr, size * nmemb, cs) &*& result <= nmemb;

// Memory management

void* malloc(size_t size);
  //@ requires true;
  //@ ensures result == 0 ? true : malloc_block(result, size) &*& chars(result, size, _);

void free(void *ptr);
  //@ requires malloc_block(ptr, ?size) &*& chars(ptr, size, _);
  //@ ensures true;

int main(int argc, char** argv) //@ : main
/*@ 
requires
  0 <= argc &*&
  [_]argv(argv, argc, ?args) &*&
  argc >= 3 &*&
  nth(1, args) == ?filename1 &*&
  nth(2, args) == ?filename2 &*&
  [1/2]string(filename1, ?fname1) &*&
  [1/2]string(filename2, ?fname2);
@*/
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
  //@ open [_]argv(argv, argc, ?args_list);
  //@ [1/2]string("r", _);
  //@ [1/2]string("w", _);
  
  from = fopen(argv[1], "r");
  to = fopen(argv[2], "w");
  buffer = malloc(100);
  //@ if(buffer != 0) { malloc_block(buffer, 100); chars(buffer, 100, _); }
  
  if(buffer == 0 || from == 0 || to == 0) { abort(); }
  
  nb_read = fread(buffer, 1, 100, from);
  //@ open chars(buffer, 100, ?cs_read);
  while(0 < nb_read)
  {
    //@ chars_split(buffer, nb_read);
    int nb_written = fwrite(buffer, 1, nb_read, to);
    //@ chars_join(buffer);
    nb_read = fread(buffer, 1, 100, from);
    //@ open chars(buffer, 100, ?cs_read);
  }
  fclose(from);
  fclose(to);
  free(buffer);
  return 0;
}
