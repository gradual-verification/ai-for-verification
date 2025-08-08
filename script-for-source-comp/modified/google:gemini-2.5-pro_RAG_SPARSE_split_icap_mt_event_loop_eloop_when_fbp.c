


typedef struct eloop *eloop;

struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};



typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    


void eloop_when(eloop x, eloop_handler *h, void *data)
{
    acquire(&x->lock);
    
    if (h != 0) {
    }
    
    x->handler = h;
    x->handlerData = data;
    
    release(&x->lock);
}
