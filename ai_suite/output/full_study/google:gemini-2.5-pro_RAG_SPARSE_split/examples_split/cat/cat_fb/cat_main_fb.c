#include "stdio.h"
#include "stdlib.h"


// TODO: make this function pass the verification
int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { fputs("Enter a file name.", stderr); return -1; }
  fp = fopen(argv[1], "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  res = fgets(buffer, 100, fp);
  while(res != 0)
    /*@
    loop_invariant
        file(fp) &*&
        malloc_block(buffer, 100) &*&
        (res == 0 ?
            chars_(buffer, 100, _)
        :
            string(buffer, ?scs) &*&
            buffer[length(scs) + 1..100] |-> _
        );
    @*/
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  free((void *)buffer);
  fclose(fp);
  return 0;
}