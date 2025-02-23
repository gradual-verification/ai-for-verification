#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};


struct cell* cell_create()
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}

void increment(struct cell* c)
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  {
  
  }
  mutex_release(c->mutex);
}
void decrement(struct cell* c)
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MIN) {
    abort();
  }
  c->x--;
  {
    
  }
  mutex_release(c->mutex);
}

int cas(struct cell* c, int old, int new)
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }
  {
    
  }
  mutex_release(c->mutex);
  return res;
}

int get(struct cell* c)
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  {
  }
  mutex_release(c->mutex);
  return res;
}


void only_allow_incrementing(struct cell* c)

{
  int x1 = get(c);
  int x2 = get(c);
  //assert x1 <= x2;
}
