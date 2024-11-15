#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

// Predicate for strings
/*@ 
predicate string(char *string, list<char> cs) = 
  chars(string, ?count, ?cs) &*& cs == append(cs, cons(0, nil));
@*/

// Fixpoint definition for word count
/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}
@*/

// Word count function with specifications
int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs);
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  char head = *string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result : result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}

// Test function with specifications
void test()
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

// Main function with specifications
int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  bool inword = false; 
  struct file* fp = 0; 
  char* buff = 0; 
  int total = 0; 
  char* res = 0;

  if(argc < 2) { 
    puts("No input file specified."); 
    return -1; 
  }
  
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant [?f]chars(buff, 100, ?scs) &*& fp != 0 &*& total >= 0 &*& total <= INT_MAX;
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
