
void inc(int* i)
{
  (*i) = (*i) + 1;
}


void address_of_param(int x) 
{
    int local_var;
    local_var = 5;
    int* ptr = &local_var; 
    inc(ptr);
    int z = local_var;
    assert(z == 6);
}
