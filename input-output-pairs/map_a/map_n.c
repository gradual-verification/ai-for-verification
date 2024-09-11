#include "stdlib.h"
#include "assert.h"

struct node {
    struct node *next;
    int value;
};

/* Description
    - Behavior: This function creates a new node with the given value and next node pointer. It sets the value and next pointer accordingly and returns the newly created node.
    - Parameters:
        - `value`: An integer value to be stored in the new node.
        - `next`: A pointer to the next node in the list.
*/
struct node *list_cons(int value, struct node *next)
{
    struct node *result = (struct node *)malloc(sizeof(struct node)); // Include the cast to make it a valid C++ program
    if (result == 0) { abort(); }
    result->value = value;
    result->next = next;
    return result;
}

/* Description
    - Behavior: This function compares two linked lists represented by nodes `n1` and `n2` to check if they contain the same elements in the same order. Returns `true` if the lists are equal, `false` otherwise.
    - Parameters:
        - `n1`: Pointer to the head of the first linked list.
        - `n2`: Pointer to the head of the second linked list.
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

/* Description
    - Behavior: This function deallocates memory for all nodes in the linked list starting from node `l` and sets the list to empty.
    - Parameter:
        - `l`: Pointer to the head of the linked list to be deallocated.
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

/* Description
    - Behavior: This function maps a custom mapping function `f` over the values in the linked list `list` and creates a new linked list with the transformed values.
    - Parameters:
        - `list`: Pointer to the head of the original linked list.
        - `f`: A pointer to the mapping function to be applied.
        - `data`: Additional data to be passed to the mapping function.
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

/* Description
    - Behavior: This function represents a specific mapping function that increments the input integer value `x` by one.
    - Parameters:
        - `data`: Additional data (not used in this case).
        - `x`: Integer value to be incremented by one.
*/
int plusOneFunc(void *data, int x)
{
    if (x == INT_MAX) abort();
    return x + 1;
}

/* Description
    - Behavior: The main function of the program that demonstrates the usage of the implemented functions. It creates a linked list, applies the `plusOneFunc` mapping function using `fmap`, compares the result with an expected list, and finally deallocates memory for all lists.
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
