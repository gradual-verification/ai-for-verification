
struct node {
  void* value;
  struct node* next;
};




typedef bool equals(void* v1, void* v2);

bool equals_impl(void* v1, void* v2)
{
  bool result = (uintptr_t)v1 == (uintptr_t)v2;
  return result;
}
