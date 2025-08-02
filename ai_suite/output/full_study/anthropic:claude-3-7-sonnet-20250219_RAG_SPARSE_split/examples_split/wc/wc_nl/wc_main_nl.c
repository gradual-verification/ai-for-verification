#include "stdlib.h"
#include "stdio.h"


/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
//@ requires [?f]string(string, ?cs) &*& true;
//@ ensures [f]string(string, cs) &*& result == wc_count(cs, inword);
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

/*@
// Helper fixpoint function to calculate word count
fixpoint int wc_count(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(c, cs0): 
      return c == ' ' ? 
        (inword ? 1 + wc_count(cs0, false) : wc_count(cs0, false)) : 
        wc_count(cs0, true);
  }
}
@*/

/*** 
 * Description:
The `main` function is the main driver of the program that reads input from a file and calculates the word count.
It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.

@param `argc` - Number of command-line arguments.
@param `argv` - Array of command-line arguments.
*/
//@ requires argc >= 0 &*& [_]argv(argv, argc, ?arguments);
//@ ensures true;
int main(int argc, char** argv)
{
  bool inword = false; struct file* fp = 0; char* buff = 0; int total = 0; char* res = 0;
  if(argc < 2) { puts("No input file specified."); return -1; }
  fp = fopen(argv[1], "r");
  buff = malloc(100);
  if(buff == 0 || fp == 0) { abort(); }
  //@ assert buff != 0;
  //@ assert fp != 0;
  //@ close chars(buff, 100, ?cs);
  res = fgets(buff, 100, fp);
  while(res != 0)
  //@ invariant fp != 0 &*& [_]file(fp) &*& buff != 0 &*& chars(buff, 100, _) &*& malloc_block_chars(buff, 100);
  {
    //@ open chars(buff, 100, _);
    //@ chars_to_string(buff);
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