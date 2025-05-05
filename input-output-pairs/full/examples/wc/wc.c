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

lemma void wcount_in_range(list<char> cs, bool inword)
  requires true;
  ensures wcount(cs, inword) >= 0 &*& wcount(cs, inword) <= length(cs) + 1;
{
  switch(cs) {
    case nil:
      if (inword) {
        assert wcount(cs, inword) == 1;
      } else {
        assert wcount(cs, inword) == 0;
      }
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
    case cons(h, t):
      wcount_in_range(t, false);
      wcount_in_range(t, true);
      if (h == 0) {
        assert wcount(cs, inword) == (inword ? 1 : 0);
      } else if (h == ' ') {
        assert wcount(cs, inword) == (inword ? 1 + wcount(t, false) : wcount(t, false));
      } else {
        assert wcount(cs, inword) == wcount(t, true);
      }
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
  }
}
@*/

int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& wcount(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  //@ open [f]string(string, cs);
  char head = * string;
  if(head == 0) {
    //@ close [f]string(string, cs);
    return inword ? 1 : 0;
  } else {
    //@ string_limits(string);
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close [f]string(string, cs);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close [f]string(string, cs);
      return result;
    }
  }
}


int main(int argc, char** argv) //@ : main
  //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
  //@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant file(fp) &*& res != 0 ? string(buff, ?scs) &*& buff[length(scs) + 1..100] |-> _ : buff[..100] |-> _;
  {
    //@ assert string(buff, ?scs);
    //@ wcount_in_range(scs, inword);
    int tmp = wc(buff, inword);
    //@ string_to_chars(buff);
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