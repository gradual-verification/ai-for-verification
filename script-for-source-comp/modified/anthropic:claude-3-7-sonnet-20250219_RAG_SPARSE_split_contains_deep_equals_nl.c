
struct node {
  void* value;
  struct node* next;
};


struct cell {
  int val;
};


typedef bool equals(void* x1, void* x2);


bool equals_cell(void* x1, void* x2)
{
    struct cell* c1 = (struct cell*)x1;
    struct cell* c2 = (struct cell*)x2;
    
    
    bool result = (c1->val == c2->val);
    
    
    return result;
}
