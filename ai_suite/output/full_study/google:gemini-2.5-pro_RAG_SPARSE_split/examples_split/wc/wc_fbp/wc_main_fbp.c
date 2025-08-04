#include "stdlib.h"
#include "stdio.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}

lemma void wcount_nonnegative(list<char> cs, bool inword)
    requires true;
    ensures 0 <= wcount(cs, inword);
{
    switch(cs) {
        case nil:
        case cons(h, t):
            wcount_nonnegative(t, false);
            wcount_nonnegative(t, true);
    }
}

lemma void wcount_bounded(list<char> cs, bool inword)
    requires true;
    ensures wcount(cs, inword) <= length(cs) + 1;
{
    switch(cs) {
        case nil:
        case cons(h, t):
            wcount_bounded(t, false);
            wcount_bounded(t, true);
    }
}
@*/


int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& wcount(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
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



// TODO: make this function pass the verification
int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& [1.0]argv(argv, argc, _);
//@ ensures true;
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  
  //@ open argv(argv, argc, _);
  //@ open argv(argv + 1, argc - 1, _);
  fp = fopen(argv[1], "r");
  
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  
  res = fgets(buff, 100, fp);
  
  while(res != 0)
  /*@
  invariant file(fp) &*& malloc_block(buff, 100) &*& total >= 0 &*& inword == false &*&
              (res == 0 ?
                  chars_(buff, 100, _)
              :
                  res == buff &*& string(buff, ?cs) &*& buff[length(cs)+1..100] |-> _ &*& length(cs) < 100
              );
  @*/
  {
    //@ assert string(buff, ?cs);
    //@ wcount_bounded(cs, false);
    int tmp = wc(buff, inword);
    //@ wcount_nonnegative(cs, false);
    if (total > INT_MAX - tmp) {
      //@ string_to_chars_(buff);
      //@ chars__join(buff);
      break;
    }
    total = total + tmp;
    
    //@ string_to_chars_(buff);
    //@ chars__join(buff);
    res = fgets(buff, 100, fp);
  }
  
  printf("%i", total);
  
  free(buff);
  fclose(fp);
  return 0;
}