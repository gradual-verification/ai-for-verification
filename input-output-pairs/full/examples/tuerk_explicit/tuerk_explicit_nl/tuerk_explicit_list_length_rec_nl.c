
struct node {
    struct node *next;
    int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The list_length_rec function calculates the length of a single linked list recursively.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_rec(struct node *node)
{
    if (node == 0) {
        return 0;
    } else {
        int length0 = list_length_rec(node->next);
        return 1 + length0;
    }
}

