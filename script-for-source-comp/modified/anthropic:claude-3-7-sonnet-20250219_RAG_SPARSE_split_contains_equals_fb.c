
struct node {
  void* value;
  struct node* next;
};






typedef bool equals(void* v1, void* v2);


bool my_equals(void* v1, void* v2) //@ : equals
{
  return (uintptr_t)v1 == (uintptr_t)v2;
}
