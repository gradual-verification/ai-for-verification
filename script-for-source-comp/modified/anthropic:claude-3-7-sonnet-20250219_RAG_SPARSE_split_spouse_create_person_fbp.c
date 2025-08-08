
struct person {
  char* name;
  struct person* spouse;
};



struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->name = 0; // Initialize name to NULL
  p->spouse = 0;
  return p;
}
