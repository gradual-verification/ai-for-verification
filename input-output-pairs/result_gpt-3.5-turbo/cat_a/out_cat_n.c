#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

/*@ // PRE: \valid(argv)
    // POST: The function reads the contents of the file provided in argv[1] and prints them to stdout.
    // NOTE: The function assumes correct handling of file operations and memory allocation.
*/
int main(int argc, char** argv)
{
  struct file* fp = 0; 
  char* buffer = 0; 
  char* res = 0;
  
  if(argc < 2) { puts("Enter a file name."); return -1; }
  //@ open here;
  fp = fopen(argv[1], "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  
  res = fgets(buffer, 100, fp);
  while(res != 0) 
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  
  free(buffer);
  fclose(fp);
  return 0;
}
