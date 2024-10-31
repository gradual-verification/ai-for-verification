#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

// Include VeriFast header for specification purposes
/*@
predicate chars(char *arr; list<char> cs) =
  arr == 0 ? cs == nil :
  chars(arr + 1, ?cs0) &*& cs == cons(*arr, cs0);

predicate malloc_block_chars(char *arr, int n) =
  malloc_block(arr, n) &*& chars(arr, ?cs) &*& length(cs) == n;

@*/

/***
 * Description:
The main function is the entry point of the program. 
It checks if a file name is provided as a command-line argument, reads the contents of the file, 
and prints them to the standard output (stdout).
  
@param argc - the number of command-line arguments passed to the program.
@param argv - the array of command-line arguments provided to the program.
*/

/*@
requires argc >= 1 &*& argv != 0 &*& [_]argv(argv, argc, _);
ensures true;
@*/
int main(int argc, char** argv)
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { puts("Enter a file name."); return -1; }
  
  fp = fopen(* (argv + 1), "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  
  /*@ 
  if (fp == 0) {
    if(buffer != 0) free(buffer);
  }
  @*/
  
  if(fp == 0 || buffer == 0) { abort(); }
  
  res = fgets(buffer, 100, fp);
  
  /*@
  while(res != 0)
  invariant chars(buffer, ?cs) &*& malloc_block_chars(buffer, 100);
  @*/
  while(res != 0) 
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  free(buffer);
  fclose(fp);
  return 0;
}
