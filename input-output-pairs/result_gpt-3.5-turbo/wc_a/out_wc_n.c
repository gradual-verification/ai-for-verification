#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

//@predicate word_counting(char* string, bool inword) = *string == 0 ? (inword ? 1 : 0) : 
  (*string == ' ' ? inword ? word_counting(string + 1, false) == 1 : word_counting(string + 1, false) == 0 : 
  inword ? word_counting(string + 1, true) == 1 : word_counting(string + 1, true) == 0);

int wc(char* string, bool inword)
  //@requires string *!= _ && inword |-> ?b;
  //@ensures word_counting(string, b) == result;
{
  char head = *string;
  if (head == 0) {
    return inword ? 1 : 0;
  } else {
    if (head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result : result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}

void test()
{
  //@assert word_counting("This line of text contains 8 words.", false) == 7;
}

int main(int argc, char** argv)
  //@requires true;
  //@ensures true;
{
  bool inword = false; 
  FILE* fp = 0; 
  char* buff = 0; 
  int total = 0; 
  char* res = 0;

  if (argc < 2) { 
    puts("No input file specified."); 
    return -1; 
  }

  fp = fopen(*(argv + 1), "r");
  buff = malloc(100);

  if (buff == 0 || fp == 0) { 
    abort(); 
  }

  res = fgets(buff, 100, fp);
  
  while (res != 0)
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
