
struct node {
    struct node *next;
    int value;
};


// TODO: make this function pass the verification
/***
 * Description:
The list_length_alt function calculates the length of a single linked list iteratively by traversing it in a for loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_alt(struct node *node)
{
    int i;
    for (i = 0; node != 0; node = node->next, i++)
    {

    }
    return i;
}
