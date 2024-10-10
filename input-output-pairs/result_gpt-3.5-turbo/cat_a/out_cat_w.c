#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

struct file;

struct file* fopen(char* filename, char* mode);
  //@ requires true;
  //@ ensures result == 0 ? true : file(result, ?contents);

void fclose(struct file* fp);
  //@ requires file(fp, ?contents);
  //@ ensures true;

char* fgets(char* buffer, int num, struct file* fp);
  //@ requires file(fp, ?contents) &*& buffer != 0 &*& num > 0;
  //@ ensures file(fp, ?newContents) &*& result == 0 ? newContents == contents : newContents == tail(contents);

struct file* abort();
  //@ requires true;
  //@ ensures false;

struct file {
};

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { puts("Enter a file name."); return -1; }
  fp = fopen(* (argv + 1), "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
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
