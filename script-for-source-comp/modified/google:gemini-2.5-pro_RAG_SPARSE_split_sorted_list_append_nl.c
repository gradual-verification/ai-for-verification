
struct node {
    int value;
    struct node *next;
};


struct node *append(struct node *head, int value)
{
    if (head == 0 || value <= head->value) {
        struct node *new_node = malloc(sizeof(struct node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->next = head;
        
        
        
        
        return new_node;
    } else {
        struct node *new_next = append(head->next, value);
        head->next = new_next;
        
        
        return head;
    }
}
