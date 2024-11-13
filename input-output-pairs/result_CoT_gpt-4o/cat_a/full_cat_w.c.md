```c
#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

//@ predicate file_pointer(FILE* fp;);
//@ predicate malloc_block_char(char* p; int count) = malloc_block(p, count);

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  struct file* fp = 0;
  char* buffer = 0;
  char* res = 0;

  if(argc < 2) 
  {
    puts("Enter a file name."); 
    return -1; 
  }

  fp = fopen(*(argv + 1), "r");
  buffer = malloc(sizeof(char) * 100); 
  if(fp == 0 || buffer == 0) 
  { 
    abort(); 
  } 
  //@ open file_pointer(fp);
  //@ open malloc_block_char(buffer, 100);

  res = fgets(buffer, 100, fp);
  //@ close file_pointer(fp);

  while(res != 0) 
  //@ loop invariant file_pointer(fp) &*& malloc_block_char(buffer, 100) &*& res == 0 || res == buffer;
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  //@ open malloc_block_char(buffer, 100);
  free(buffer);
  //@ close file_pointer(fp);
  fclose(fp);
  return 0;
}
```
