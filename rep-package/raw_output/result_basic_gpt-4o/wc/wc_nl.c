#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"
#include "verifast.h"

/*@
predicate string(char *s, list<char> cs) =
  *s == 0 ? cs == nil : s[0..1] |-> ?c &*& string(s + 1, ?cs2) &*& cs == cons(c, cs2);
  
fixpoint list<list<char>> split_words(list<char> cs) {
    switch(cs) {
        case nil: return nil;
        case cons(c, cs2): return (c == ' ' ? cons(nil, split_words(cs2)) : switch(split_words(cs2)) { case nil: return cons(cons(c, nil), nil); case cons(w, ws): return cons(cons(c, w), ws); });
    }
}

fixpoint int word_count(list<char> cs) {
    return length(filter((ws) -> length(ws) > 0, split_words(cs)));
}

@*/

/***
 * Description:
 * The `wc` function calculates the word count in a given string.
 *
 * @param `string` - The string to count words in.
 * @param `inword` - A boolean flag indicating whether the current position is inside a word or not.
*/
//@ requires string(string, ?cs);
//@ ensures string(string, cs) &*& result == word_count(cs);
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

/*** 
 * Description:
 * The `test` function is a test function to validate the `wc` function.
 */
void test()
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  // The string has 7 words (8 is a typo in the comment)
  assert(nb == 7);
}

/*** 
 * Description:
 * The `main` function is the main driver of the program that reads input from a file and calculates the word count.
 * It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.
 *
 * @param `argc` - Number of command-line arguments.
 * @param `argv` - Array of command-line arguments.
 */
int main(int argc, char** argv)
//@ requires true;
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
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }
  printf("%i", total);
  free(buff);
  fclose(fp);
  return 0;
}
