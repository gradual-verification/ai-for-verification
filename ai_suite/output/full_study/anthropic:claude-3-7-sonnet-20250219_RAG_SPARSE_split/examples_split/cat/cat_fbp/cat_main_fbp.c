#include "stdio.h"
#include "stdlib.h"


// TODO: make this function pass the verification
int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { fputs("Enter a file name.", stderr); return -1; }
  
  //@ open [_]argv(argv, argc, _);
  //@ assert [_]string(argv[1], ?filename);
  
  fp = fopen(argv[1], "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  
  if(fp == 0 || buffer == 0) { abort(); }
  
  //@ assert file(fp);
  //@ assert chars_(buffer, 100, _);
  
  res = fgets(buffer, 100, fp);
  while(res != 0) 
  {
    //@ assert string(buffer, ?line);
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  free((void *)buffer);
  fclose(fp);
  return 0;
}