

// TODO: make this function pass the verification
/* Description
    - Behavior: This function removes a specific element from the list segment starting from *phead*.
    - Parameters: *phead* is a pointer to the head of the list segment, *element* is the node that needs to be removed

It requires that element is part of the list segment starting from *phead*.
IT ensures that The list segment doesn't have element anymore.
*/
void lseg_remove(void *phead, void *element)
{
    void **pnext = phead;
    while (*pnext != element)
    {
        void **next = *pnext;
        pnext = next;
    }
    {
        void *nextNext = *((void **)*pnext);
        *pnext = nextNext;
    }
}
