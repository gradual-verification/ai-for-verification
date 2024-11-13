#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

/*@ 
predicate malloc_block_char(char *p; int count) = malloc_block(p, count);

requires true;
ensures result == 0;
*/
int abort();

/**@
requires argc >= 1 &*& 
         [?f]argv[0..argc] |-> char* &*& 
         malloc_block_char(_) &*&
         (argc > 1 ? [?g]argv[1] |-> char* : true);
ensures result == 0;
*/
int main(int argc, char** argv)
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;

  if(argc < 2) { puts("Enter a file name."); return -1; }

  fp = fopen(*(argv + 1), "r");
  buffer = malloc(sizeof(char) * 100);

  if(fp == 0 || buffer == 0) { abort(); }

  res = fgets(buffer, 100, fp);

  /*@ 
  loop_invariant buffer != 0 &*& fp != 0;
  */
  while(res != 0) 
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }

  free(buffer);
  fclose(fp);

  return 0;
}
