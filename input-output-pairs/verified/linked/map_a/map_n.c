#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/***
 * Description:
The list_cons function creates a new node with the given `value` and link this node to a given `next` node. 
It returns the newly created node.

@param `value` - an integer value to be stored in the new node.
@param `next` - a pointer to the next node in the list.
*/
struct node *list_cons(int value, struct node *next)
{
    struct node *result = (struct node *)malloc(sizeof(struct node));
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    return result;
}

/***
 * Description:
The equals function compares two linked lists represented by nodes `n1` and `n2` to check if they contain the same elements in the same order. 
Returns `true` if the lists are equal, `false` otherwise.

@param `n1` - pointer to the head of the first linked list.
@param `n2` - pointer to the head of the second linked list.
*/
bool equals(struct node *n1, struct node *n2)
{
    bool result = false;
    if (n1 == 0)
        result = n2 == 0;
    else if (n2 == 0)
        result = false;
    else if (n1->value != n2->value)
        result = false;
    else {
        bool tmp = equals(n1->next, n2->next);
        result = tmp;
    }
    return result;
}

/*** 
 * Description:
The dispose function deallocates memory for all nodes in the linked list starting from node `l` and sets the list to empty.

@param `l` - pointer to the head of the linked list to be deallocated.
*/
void dispose(struct node *l)
{
    if (l != 0) {
        struct node *next = l->next;
        free(l);
        dispose(next);
    }
}

typedef int (* mapfunc)(void *data, int x);

/*** 
 * Description:
The fmap function maps a custom mapping function `f` over the values in the linked list `list` and creates a new linked list with the transformed values.

@param `list` - pointer to the head of the original linked list.
@param `f` - a pointer to the mapping function to be applied.
@param `data` - additional data to be passed to the mapping function.
*/
struct node *fmap(struct node *list, mapfunc f, void *data)
{
    if (list == 0) {
        return 0;
    } else {
        int fvalue = f(data, list->value);
        struct node *fnext = fmap(list->next, f, data);
        struct node *result = list_cons(fvalue, fnext);
        return result;
    }
}

/*** 
 * Description:
The plusOneFunc function represents a specific mapping function that increments the input integer value `x` by one.

@param `data` - additional data (not used in this case).
@param `x` - integer value to be incremented by one.
*/
int plusOneFunc(void *data, int x)
{
    if (x == INT_MAX) abort();
    return x + 1;
}

/*** 
 * Description:
The main function of the program that demonstrates the usage of the implemented functions. 
It creates a linked list, applies the `plusOneFunc` mapping function using `fmap`, 
compares the result with an expected list, and finally deallocates memory for all lists.
*/
int main()
{
    struct node *l = 0;
    l = list_cons(3, l);
    l = list_cons(2, l);
    l = list_cons(1, l);
    struct node *l2 = fmap(l, plusOneFunc, 0);
    struct node *l3 = 0;
    l3 = list_cons(4, l3);
    l3 = list_cons(3, l3);
    l3 = list_cons(2, l3);
    bool tmp = equals(l2, l3);
    assert(tmp);
    dispose(l);
    dispose(l2);
    dispose(l3);
    return 0;
}
