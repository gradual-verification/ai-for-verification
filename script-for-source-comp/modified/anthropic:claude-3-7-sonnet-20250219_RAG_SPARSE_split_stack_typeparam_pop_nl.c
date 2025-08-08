  


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


void* pop(struct stack* stack)
{
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();  // or handle error as necessary
  }
  stack->size--;
  return data;
}
