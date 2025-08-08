

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

struct data* create_data(int foo, int bar)
{
  struct data* data = malloc(sizeof(struct data));
  if (data == 0) abort();
  
  data->foo = foo;
  data->bar = bar;
  return data;
}
