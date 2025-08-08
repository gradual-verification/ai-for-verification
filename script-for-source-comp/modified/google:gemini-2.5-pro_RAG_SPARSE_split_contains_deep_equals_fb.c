
struct node {
  void* value;
  struct node* next;
};


typedef bool equals(void* x1, void* x2);



struct cell {
  int val;
};



bool cell_equals(void* x1, void* x2) //@ : equals
{
  
  struct cell* c1 = (struct cell*)x1;
  struct cell* c2 = (struct cell*)x2;
  
  bool res = c1->val == c2->val;
  
  
  
  return res;
}
