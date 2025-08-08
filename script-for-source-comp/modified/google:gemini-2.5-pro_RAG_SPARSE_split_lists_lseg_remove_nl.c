

void lseg_remove(void *phead_void, void *element)
{
    void **phead = (void **)phead_void;
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
