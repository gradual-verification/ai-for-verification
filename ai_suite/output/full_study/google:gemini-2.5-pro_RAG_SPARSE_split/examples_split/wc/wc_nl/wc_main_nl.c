#include "stdlib.h"
#include "stdio.h"

/*@
fixpoint int wc_spec(list<char> cs, bool inword) {
    switch(cs) {
        case nil: return inword ? 1 : 0;
        case cons(h, t):
            if (h == ' ') {
                int result = wc_spec(t, false);
                return inword ? 1 + result : result;
            } else {
                int result = wc_spec(t, true);
                return result;
            }
    }
}

lemma void wc_spec_nonneg(list<char> cs, bool inword)
    requires true;
    ensures wc_spec(cs, inword) >= 0;
{
    switch(cs) {
        case nil:
        case cons(h, t):
            wc_spec_nonneg(t, false);
            wc_spec_nonneg(t, true);
    }
}
@*/

/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
int wc(char* string, bool inword)
    //@ requires string(string, ?cs);
    //@ ensures string(string, cs) &*& result == wc_spec(cs, inword);
{
  //@ open string(string, cs);
  char head = *string;
  if(head == 0) {
    //@ close string(string, cs);
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close string(string, cs);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close string(string, cs);
      return result;
    }
  }
}



// TODO: make this function pass the verification
/*** 
 * Description:
The `main` function is the main driver of the program that reads input from a file and calculates the word count.
It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.

@param `argc` - Number of command-line arguments.
@param `argv` - Array of command-line arguments.
*/
int main(int argc, char** argv) //@ : main
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  res = fgets(buff, 100, fp);
  while(res != 0)
    /*@
    invariant file(fp) &*& malloc_block(buff, 100) &*&
              (res == 0 ?
                  chars_(buff, 100, _)
              :
                  res == buff &*& string(buff, ?cs) &*& buff[length(cs) + 1..100] |-> _
              ) &*&
              inword == false &*&
              INT_MIN <= total &*& total <= INT_MAX;
    @*/
  {
    //@ assert string(buff, ?cs);
    int tmp = wc(buff, inword);
    //@ wc_spec_nonneg(cs, inword);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    //@ string_to_chars_(buff);
    //@ chars__join(buff);
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  if (res != 0) {
    //@ string_to_chars_(buff);
    //@ chars__join(buff);
  }
  free(buff);
  fclose(fp);
  return 0;
}