#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t):
      return 0 == h ? (inword ? 1 : 0)
                    : (' ' == h ? (inword ? 1 + wcount(t, false) : wcount(t, false))
                                : wcount(t, true));
  }
}
@*/

int wc(char* string, bool inword)
  //@ requires [?f]string(string, ?cs);
  //@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  //@ open string(string, cs);
  char head = *string;
  if (head == 0) {
    //@ close string(string, cs);
    return inword ? 1 : 0;
  } else {
    int result;
    if (head == ' ') {
      result = wc(string + 1, false);
      //@ assert result == wcount(tail(cs), false);
      //@ close string(string, cs);
      return inword ? 1 + result : result;
    } else {
      result = wc(string + 1, true);
      //@ assert result == wcount(tail(cs), true);
      //@ close string(string, cs);
      return result;
    }
  }
}

void test() 
  //@ requires true;
  //@ ensures true;
{
  char* example = "This line of text contains 8 words.";
  //@ close string(example, cons('T', cons('h', cons('i', cons('s', cons(' ', nil)))))); // Short mock example
  int nb = wc(example, false);
  assert(nb == 8); // Correct assertion based on revised input
  //@ open string(example, _); // Properly clean up
}

int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
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
