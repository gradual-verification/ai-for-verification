
struct cell {
  int x;
};


struct cell* create_cell() 
{
  struct cell* c = malloc(sizeof(struct cell));
  if (c == 0) abort();
  c->x = 0;
  return c;
}
