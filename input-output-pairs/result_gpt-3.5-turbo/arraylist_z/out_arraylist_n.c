#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct arraylist {
  void **data;
  int size;
  int capacity;
};

//@predicate arraylist(struct arraylist* a; list<void *> elements) = a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*& data[0..size] |-> elements &*& capacity >= size &*& capacity >= 0 &*& size >= 0 &*& size <= capacity ;

//@requires true;
//@ensures \result != 0 ==> malloc_block_arraylist(\result) &*& arraylist(\result, nil) &*& \result->size == 0 &*& \result->capacity == 100;
struct arraylist *create_arraylist();

//@requires arraylist(a, ?elements) &*& 0 <= i &*& i < length(elements);
//@ensures arraylist(a, elements) &*& \result == elements[i];
void *list_get(struct arraylist *a, int i);

//@requires arraylist(a, ?elements);
//@ensures arraylist(a, elements) &*& \result == length(elements);
int list_length(struct arraylist *a);

//@requires arraylist(a, ?elements);
//@ensures arraylist(a, append(elements, cons(v, nil)));
void list_add(struct arraylist *a, void *v);

//@requires arraylist(a, ?elements) &*& 0 <= n &*& n < length(elements);
//@ensures arraylist(a, append(take(n, elements), drop(n+1, elements)));
void list_remove_nth(struct arraylist *a, int n);

//@requires arraylist(a, ?elements);
//@ensures true;
void list_dispose(struct arraylist* a);

int main()
//@requires true;
//@ensures true;
{
  struct arraylist* a = create_arraylist();
  void* tmp = 0;
  list_add(a, (void *)10);
  list_add(a, (void *)20);
  
  tmp = list_get(a, 1);
  assert(tmp == (void*)20);
  list_dispose(a);

  return 0;
}
