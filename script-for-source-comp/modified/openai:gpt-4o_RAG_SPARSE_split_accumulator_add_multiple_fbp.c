
struct Accumulator {
  int total;
  int count;
};


void add_multiple(struct Accumulator* a, int n, int x)
{
  int i = 0;
  while (i < n)
  {
    if (a->total > INT_MAX - x) abort(); // Prevent overflow
    if (a->count > INT_MAX - 1) abort(); // Prevent overflow
    a->total += x;
    a->count += 1;
    i++;
  }
}
