  


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





typedef void destructor/*@<T>(predicate(void *, T) Ownership)@*/(void* data);


void destroy_stack/*@ <T> @*/(struct stack* stack)
{
  struct node* current = stack->first;
  destructor* destructor_fn = stack->destructor;
  
  while (current != 0)
  {
    struct node* next = current->next;
    destructor_fn(current->data);
    free(current);
    current = next;
  }
  free(stack);
}
