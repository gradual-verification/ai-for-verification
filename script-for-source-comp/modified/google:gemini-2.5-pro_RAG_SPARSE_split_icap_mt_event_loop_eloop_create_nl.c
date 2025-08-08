


typedef struct eloop *eloop;

struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};


typedef void eloop_handler(void *data);



eloop eloop_create()
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    
    init(&x->lock);
    
    release(&x->lock);
    
    return x;
}
