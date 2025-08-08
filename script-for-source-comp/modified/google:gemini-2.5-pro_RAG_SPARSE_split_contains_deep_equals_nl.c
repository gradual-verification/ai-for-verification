
struct node {
  void* value;
  struct node* next;
};


struct cell {
  int val;
};


typedef bool equals(void* x1, void* x2);
