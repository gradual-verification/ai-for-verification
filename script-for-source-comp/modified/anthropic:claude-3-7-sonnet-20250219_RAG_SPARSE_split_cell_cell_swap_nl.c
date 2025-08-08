
struct cell {
  int x;
};


void cell_set(struct cell* c, int v)
{
  c->x = v;
}


int cell_get(struct cell* c)
{
  int result = c->x;
  return result;
}


void cell_swap(struct cell* c1, struct cell* c2)
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}
