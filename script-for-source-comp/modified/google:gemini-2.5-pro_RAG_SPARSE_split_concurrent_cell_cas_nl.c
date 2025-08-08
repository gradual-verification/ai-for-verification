

struct cell {
  int x;
  struct mutex* mutex;
};


int cas(struct cell* c, int old, int new)
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  } else {
  }
  {
    
  }
  mutex_release(c->mutex);
  return res;
}
