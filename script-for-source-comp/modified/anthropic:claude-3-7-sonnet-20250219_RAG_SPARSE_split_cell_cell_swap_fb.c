
struct cell {
  int x;
};



void cell_set(struct cell* c, int v)
{
  c->x = v;
}


int cell_get(struct cell* c)
{
  return c->x;
}


void cell_swap(struct cell* c1, struct cell* c2)
{
  int tmp1 = c1->x;
  int tmp2 = c2->x;
  c1->x = tmp2;
  c2->x = tmp1;
}

struct cell {
  int x;
};



void cell_set(struct cell* c, int v)
{
  c->x = v;
}


int cell_get(struct cell* c)
{
  return c->x;
}


void cell_swap(struct cell* c1, struct cell* c2)
{
  int tmp1 = cell_get(c1);
  int tmp2 = cell_get(c2);
  cell_set(c1, tmp2);
  cell_set(c2, tmp1);
}
