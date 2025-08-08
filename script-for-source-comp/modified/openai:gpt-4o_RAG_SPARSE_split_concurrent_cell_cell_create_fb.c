
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
  if (m == 0) {
    free(c);
    return 0;
  }
  c->mutex = m;
  return c;
}
