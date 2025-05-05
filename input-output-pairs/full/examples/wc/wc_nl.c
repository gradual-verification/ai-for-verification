#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
int wc(char* string, bool inword)
{
  char head = * string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}


/*** 
 * Description:
The `main` function is the main driver of the program that reads input from a file and calculates the word count.
It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.

@param `argc` - Number of command-line arguments.
@param `argv` - Array of command-line arguments.
*/
int main(int argc, char** argv)
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  {
    int tmp = wc(buff, inword);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  return 0;
}