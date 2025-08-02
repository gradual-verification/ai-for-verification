#include "stdio.h"
#include "stdlib.h"


// TODO: make this function pass the verification
int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  
  //@ open argv(argv, argc, _);
  if(argc < 2) { fputs("Enter a file name.", stderr); return -1; }
  
  fp = fopen(argv[1], "r");
  //@ if (fp == 0) {}
  
  buffer = malloc(sizeof(char) * 100);
  //@ if (buffer == 0) {}
  
  res = 0;
  
  if(fp == 0 || buffer == 0) { abort(); }
  
  //@ assert chars_(buffer, 100, _);
  
  res = fgets(buffer, 100, fp);
  
  //@ assert [_]file(fp);
  
  while(res != 0) 
  //@ invariant [_]file(fp) &*& chars_(buffer, 100, _);
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  free((void *)buffer);
  fclose(fp);
  return 0;
}