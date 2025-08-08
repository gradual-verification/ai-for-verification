





void atomic_dec(int* c);

void atomic_dec(int* c) {
  int old_value = *c;
  *c = old_value - 1;
}
