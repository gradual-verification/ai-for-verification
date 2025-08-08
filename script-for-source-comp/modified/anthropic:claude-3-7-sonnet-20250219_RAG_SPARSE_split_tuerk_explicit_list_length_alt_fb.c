struct node {
    struct node *next;
    int value;
};



int list_length_alt(struct node *node)
{
    int i;
    struct node *current = node;
    for (i = 0; node != 0; node = node->next, i++)
    {
    }
    return i;
}
