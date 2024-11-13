#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h"
#include "assert.h"
#include "verifast.h"

// Predicate to represent valid string
predicate valid_string(char *s, int length) =
    s == 0 ? length == 0 : s[0] != 0 &*& valid_string(s + 1, length - 1);

// Function that calculates the word count in a given string
/*@
    requires valid_string(string, length) &*& length >= 0;
    ensures  valid_string(string, length) &*& result >= 0;
@*/
int wc(char* string, bool inword)
{
  char head = *string;
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

// Test function to validate the `wc` function
void test()
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

// Function that reads input from a file and calculates the word count
/*@
    requires argc > 0 &*& [_]argv[0..argc] != 0 &*& [_]argv[1..argc] != 0;
    ensures result == 0 || result == -1;
@*/
int main(int argc, char** argv)
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  /*@
    invariant total >= 0;
    invariant buff[0..100] == _ &*& valid_string(buff, 100);
  @*/
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
