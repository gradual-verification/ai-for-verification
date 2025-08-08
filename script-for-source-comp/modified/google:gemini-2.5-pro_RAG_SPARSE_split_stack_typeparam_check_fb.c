


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



struct stack* create_empty_stack/*@ <T> @*/(destructor* destructor)
{
  struct stack* stack = malloc( sizeof( struct stack ) );
  if ( stack == 0 ) abort();
  
  stack->destructor = destructor;
  stack->first = 0;
  stack->size = 0;
  
  return stack;
}


void destroy_stack/*@ <T> @*/(struct stack* stack)
{
  destructor* destructor = stack->destructor;
  struct node* current = stack->first;
  
  while ( current != 0 )
  {
    struct node* next = current->next;
    destructor(current->data);
    free(current);
    current = next;
  }
  
  free(stack);
}


void push/*@ <T> @*/(struct stack* stack, void* data)
{
  struct node* node = malloc( sizeof( struct node ) );
  if ( node == 0 ) abort();

  node->data = data;
  node->next = stack->first;
  stack->first = node;
  if (stack->size == INT_MAX) {
    abort();
  }
  stack->size++;
}


void* pop/*@ <T> @*/(struct stack* stack)
{
  struct node* first = stack->first;
  void* data = first->data;
  stack->first = first->next;
  free(first);
  if (stack->size == INT_MIN) {
    abort();
  }
  stack->size--;
  return data;
}


int size/*@ <T> @*/(struct stack* stack)
{
  int size = stack->size;
  return size;
}



struct data* create_data(int foo, int bar)
{
  struct data* data = malloc( sizeof( struct data ) );
  if ( data == 0 ) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}


void destroy_data(void* data)
{
  free(data);
}


void check()
{
  struct stack* stack = create_empty_stack<DataCarrier>(destroy_data);
  int s = size(stack);
  assert s == 0;
  
  struct data* data = create_data(1, 2);
  push(stack, data);
  
  s = size(stack);
  
  data = create_data(2, 3);
  push(stack, data);

  s = size(stack);
  assert s == 2;
  
  struct data* popped = pop(stack);
  destroy_data(popped);

  destroy_stack(stack);
}
