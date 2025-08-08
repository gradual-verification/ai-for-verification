
struct Counter {
  int value;
};



bool random()
{
    return true;
}

struct Counter* create_counter()
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) abort();
  c->value = 0;
  return c;
}

void inc(struct Counter* c)
{
  c->value = c->value + 1;
}

void swap(struct Counter* c1, struct Counter* c2)
{
  int temp = c1->value;
  c1->value = c2->value;
  c2->value = temp;
}

int counter_get(struct Counter* c)
{
  int result = c->value;
  return result;
}

void dispose(struct Counter* c)
{
  free(c);
}
