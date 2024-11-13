#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@ 
predicate malloc_block(char *p; int size) = malloc_block_chars(p, size, _);
predicate valid_string(char *string;) = string(string, ?cs) &*& malloc_block(string, length(cs) + 1);
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}
@*/

int wc(char* string, bool inword)
//@ requires [?f]valid_string(string);
//@ ensures [f]valid_string(string) &*& result == wcount(string, inword);
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

void test() 
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  //@ open valid_string(buff);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  //@ close valid_string(buff);
  while(res != 0)
  //@ invariant valid_string(buff) &*& total >= 0 &*& total + wcount(buff, inword) <= INT_MAX;
  {
    //@ open valid_string(buff);
    int tmp = wc(buff, inword);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
    //@ close valid_string(buff);
  }
  printf("%i", total);
  free(buff);
  //@ leak malloc_block(buff, 100);
  fclose(fp);
  return 0;
}
