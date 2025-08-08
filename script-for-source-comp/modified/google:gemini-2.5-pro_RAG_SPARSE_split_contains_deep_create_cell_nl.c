
struct node {
  void* value;
  struct node* next;
};


struct cell {
  int val;
};


struct cell* create_cell(int v)
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) abort();
  c->val = v;
  return c;
}
