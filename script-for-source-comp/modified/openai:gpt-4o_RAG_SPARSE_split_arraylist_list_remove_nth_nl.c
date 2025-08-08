

struct arraylist {
  void **data;
  int size;
  int capacity;
};

    0 <= size &*& size <= capacity &*&
    pointers(data, capacity, ?elems) &*&
    elements == take(size, elems);

void list_remove_nth(struct arraylist *a, int n)
{
  void** data = a->data;
  int size = a->size;
  memmove(data + n, data + n + 1, (unsigned int) (size - n - 1) * sizeof(void *));
  a->size = a->size - 1;
}
