#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  FILE* fp = 0; 
  char* buffer = 0; 
  char* res = 0;
  
  if(argc < 2) { 
    puts("Enter a file name."); 
    return -1; 
  }
  
  fp = fopen(argv[1], "r");
  //@ assert fp == 0 || fp != 0; // file pointer can either be null or valid
  
  buffer = malloc(sizeof(char) * 100);
  //@ assert buffer == 0 || buffer != 0; // buffer can either be null or valid
  
  res = 0;
  
  if(fp == 0 || buffer == 0) { 
    abort(); 
  }
  
  res = fgets(buffer, 100, fp);
  
  while(res != 0) 
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  free(buffer);
  fclose(fp);
  
  return 0;
}
