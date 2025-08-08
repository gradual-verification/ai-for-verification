struct node {
    struct node *next;
    int value;
};



int list_length(struct node *node)
{
    int i = 0;
    struct node *current = node;
    
    while (current != 0)
    {
        current = current->next;
        i++;
    }
    
    return i;
}
struct node {
    struct node *next;
    int value;
};



int list_length(struct node *node)
{
    int i = 0;
    struct node *current = node;
    
    
    while (current != 0)


int list_length(struct node *node)
{
    int i = 0;
    struct node *current = node;
    
    
    while (current != 0)
    {
        current = current->next;
        i++;
    }
    
    return i;
}
struct node {
    struct node *next;
    int value;
};



int list_length(struct node *node)
{
    int i = 0;
    struct node *current = node;
    
    
    while (current != 0)
    {
        struct node *next = current->next;
        i++;
        current = next;
    }
    
    
    return i;
}
