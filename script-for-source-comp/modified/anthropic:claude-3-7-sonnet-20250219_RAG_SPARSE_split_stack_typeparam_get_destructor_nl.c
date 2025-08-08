  


struct node
{
  void* data;
  struct node* next;
};

struct stack
{
  struct node* first;
  destructor* destructor;
  int size;
};



struct data
{
  int foo;
  int bar;
};




typedef void destructor(void* data);



destructor* get_destructor(struct stack* stack)
{
  destructor* d = stack->destructor;
  return d;
}
