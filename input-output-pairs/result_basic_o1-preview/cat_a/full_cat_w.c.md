```c
#include "stdio.h"
#include "stdlib.h"

//@ #include <lists.gh>

/* Function Specifications */

predicate malloc_block(void *p; int size);
predicate chars(char *p; int count; list<char> cs);
predicate string(char *p; list<char> cs) = chars(p, ?n, cs) &*& mem('\0', cs) == true &*& n == length(cs);
predicate file_handle(struct file *f);

struct file* fopen(char *filename, char *mode);
  //@ requires [?f1]string(filename, ?cs1) &*& [?f2]string(mode, ?cs2);
  //@ ensures result == 0 ? true : file_handle(result);

int fclose(struct file *stream);
  //@ requires file_handle(stream);
  //@ ensures true;

char *fgets(char *str, int num, struct file *stream);
  //@ requires chars(str, num, _) &*& file_handle(stream);
  //@ ensures result == 0 ? chars(str, num, _) : string(str, ?cs);

int puts(char *str);
  //@ requires [?f]string(str, ?cs);
  //@ ensures true;

void *malloc(int size);
  //@ requires true;
  //@ ensures result == 0 ? true : malloc_block(result, size);

void free(void *p);
  //@ requires malloc_block(p, _);
  //@ ensures true;

/* Main Function */
int main(int argc, char **argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  struct file *fp = 0;
  char *buffer = 0;
  char *res = 0;

  if(argc < 2) {
    puts("Enter a file name.");
    return -1;
  }

  //@ open [_]argv(argv, argc, ?args);
  //@ assert args[1] == ?filename;
  fp = fopen(argv[1], "r");
  //@ if (fp != 0) { close file_handle(fp); }

  buffer = malloc(sizeof(char) * 100);
  //@ if (buffer != 0) { close malloc_block(buffer, 100); }

  if(fp == 0 || buffer == 0) { abort(); }

  //@ open malloc_block(buffer, 100);
  //@ chars(buffer, 100, _);

  res = fgets(buffer, 100, fp);
  //@ if(res == 0) { close chars(buffer, 100, _); }

  while(res != 0)
    //@ invariant file_handle(fp) &*& res != 0 ? string(buffer, ?cs) : chars(buffer, 100, _);
  {
    puts(buffer);
    //@ string_to_chars(buffer);
    res = fgets(buffer, 100, fp);
    //@ if(res == 0) { close chars(buffer, 100, _); }
  }

  //@ close malloc_block(buffer, 100);
  free(buffer);
  fclose(fp);

  return 0;
}
```
