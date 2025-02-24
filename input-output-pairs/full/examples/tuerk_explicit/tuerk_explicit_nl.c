// Illustrates VeriFast's implementation of the alternative loop proof rule proposed by [1].
// [1] Thomas Tuerk. Local Reasoning about While-Loops. VS-Theory workshop at VSTTE 2010.

struct node {
    struct node *next;
    int value;
};

/***
 * Description:
The list_length function calculates the length of a single linked list iteratively by traversing it in a while loop.

@param node: the starting node of the linkedlist, and null means that the linkedlist is empty.
*/
int list_length(struct node *node)
{
    int i = 0;
    while (node != 0)
    {
        node = node->next;
        i++;
    }
    return i;
}

/***
 * Description:
The list_length_alt function calculates the length of a single linked list iteratively by traversing it in a for loop.

@param node: the starting node of the linkedlist, and null means that the linkedlist is empty.
*/
int list_length_alt(struct node *node)
{
    int i;
    for (i = 0; node != 0; node = node->next, i++)
    {

    }
    return i;
}
