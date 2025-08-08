

struct arraylist {
  void **data;
  int size;
  int capacity;
};


void *list_get(struct arraylist *a, int i)
{
  void *result = a->data[i];
  return result;
}
