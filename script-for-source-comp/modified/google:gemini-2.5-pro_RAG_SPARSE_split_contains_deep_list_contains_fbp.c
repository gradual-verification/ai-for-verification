
struct node {
  void* value;
  struct node* next;
};




struct cell {
  int val;
};



typedef bool equals(void* x1, void* x2);


bool list_contains(struct node* n, void* v, equals* eq) 
{
  if(n == 0) {
    return false;
  } else {
    bool cont = eq(v, n->value);
    if(cont) {
      return true;
    } else {
      cont = list_contains(n->next, v, eq);
      return cont;
    }
  }
}
