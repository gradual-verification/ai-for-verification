#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"
// #include "verifast.h"

/*@
  
//fixpoint list<list<char>> split_words(list<char> cs) {
//    switch(cs) {
//        case nil: return nil;
//       case cons(c, cs2): return (c == ' ' ? cons(nil, split_words(cs2)) : switch(split_words(cs2)) { case nil: return cons(cons(c, nil), nil); case cons(w, ws): return cons(cons(c, w), ws); });
//    }
//}

//fixpoint int word_count(list<char> cs) {
//    return length(filter((ws) -> length(ws) > 0, split_words(cs)));
//}

fixpoint int word_count(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + word_count(t, false)) : word_count(t, true));
  }
}

lemma void word_count_in_range(list<char> cs, bool inword)
  requires true;
  ensures word_count(cs, inword) >= 0 &*& word_count(cs, inword) <= length(cs) + 1;
{
  switch(cs) {
    case nil:
      // Base case: if the list is empty, word_count(cs, inword) is either 0 or 1,
      // and length(cs) is 0, so the result is valid.
      if (inword) {
        assert word_count(cs, inword) == 1;
      } else {
        assert word_count(cs, inword) == 0;
      }
      assert word_count(cs, inword) <= length(cs) + 1;
      break;
    case cons(h, t):
      // Recursive case: process the head and the tail of the list.
      word_count_in_range(t, false); // Call lemma for tail with false
      word_count_in_range(t, true);  // Call lemma for tail with true
      if (h == 0) {
        // If head is the null character, word_count(cs, inword) is either 0 or 1,
        // which is still less than or equal to length(cs).
        assert word_count(cs, inword) == (inword ? 1 : 0);
      } else if (h == ' ') {
        // If the head is a space, the word_count either increments or remains the same.
        // The word count is still less than or equal to the total length.
        assert word_count(cs, inword) == (inword ? 1 + word_count(t, false) : word_count(t, false));
      } else {
        // If the head is a non-space character, we proceed with the count from the tail.
        assert word_count(cs, inword) == word_count(t, true);
      }
      // Finally, assert that word_count(cs, inword) is less than or equal to length(cs).
      assert word_count(cs, inword) <= length(cs) + 1;
      break;
  }
}
@*/

/***
 * Description:
 * The `wc` function calculates the word count in a given string.
 *
 * @param `string` - The string to count words in.
 * @param `inword` - A boolean flag indicating whether the current position is inside a word or not.
*/

int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& word_count(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == word_count(cs, inword);
{
  char head = * string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
      //@ string_limits(string);
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
    //@ word_count_in_range(scs, inword);
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
