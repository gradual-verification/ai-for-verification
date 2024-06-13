#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include "bool.h"
#include "assert.h"

/* Description:
  - Behavior: This function calculates the word count in a given string.
  - Parameters:
      - `char* string`: The string to count words in.
      - `bool inword`: A boolean flag indicating whether the function is currently inside a word or not.
*/
This function calculates the word count in a given string. 
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

/* Description:
  - Behavior: This function is a test function to validate the `wc` function.
*/
void test()
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

/* Description:
  - Behavior: This function is the main driver of the program that reads input from a file and calculates the word count.
  - Parameters:
    - `int argc`: Number of command-line arguments.
    - `char** argv`: Array of command-line arguments.
*/
int main(int argc, char** argv)
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(* (argv + 1), "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  {
    int tmp = wc(buff, inword);
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  return 0;
}