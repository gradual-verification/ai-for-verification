#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


// TODO: make this function pass the verification
/*cell_create function
-param: none
-description: This function creates a new cell with an intialized mutex in it.

It returns a pointer to the newly created cell.
*/
struct cell* cell_create()
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}

