
struct node {
  void* value;
  struct node* next;
};


struct cell {
  int val;
};


struct node* add(struct node* n, void* v) 
{
  struct node* nn = malloc(sizeof(struct node));
  if(nn == 0) abort();
  nn->value = v;
  nn->next = n;
  return nn;
}
