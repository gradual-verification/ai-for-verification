#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}

predicate valid_string(char *string;) =
  string != 0 &*& [?f]string(string, _);

lemma_auto void string_non_null() 
  requires [?f]string(?s, _) &*& s != 0;
  ensures [f]string(s, _);
{
}

@*/

int wc(char* string, bool inword)
//@ requires valid_string(string);
//@ ensures valid_string(string) &*& result == wcount(chars(string), inword);
{
  //@ open valid_string(string);
  char head = *string;
  if (head == 0) {
    //@ close valid_string(string);
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
  //@ close valid_string(string);
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
  bool inword = false;
  struct file* fp = 0;
  char* buff = 0;
  int total = 0;
  char* res = 0;

  if (argc < 2) {
    puts("No input file specified.");
    return -1;
  }

  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if (buff == 0 || fp == 0) {
    abort();
  }

  //@ close valid_string(buff);
  res = fgets(buff, 100, fp);

  while (res != 0)
  /*@ invariant [0.5]valid_string(buff) &*&
                0 <= total &*&
                total <= INT_MAX;
  @*/
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
