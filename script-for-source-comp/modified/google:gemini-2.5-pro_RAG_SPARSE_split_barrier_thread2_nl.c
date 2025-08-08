
struct barrier {
    struct mutex *mutex;
    int n;
    int k;
    bool outgoing;
};

struct data {
    struct barrier *barrier;
    int x1;
    int x2;
    int y1;
    int y2;
    int i;
};


void barrier(struct barrier *b)
{
    struct mutex *mutex = b->mutex;
    mutex_acquire(mutex);

    while (b->outgoing)
    {
        mutex_release(mutex);
        mutex_acquire(mutex);
    }

    b->k++;
    if (b->k == b->n) {
        b->outgoing = true;
        b->k--;
        mutex_release(b->mutex);
    } else {
        while (!b->outgoing)
        {
            mutex_release(mutex);
            mutex_acquire(mutex);
        }
        b->k--;
        if (b->k == 0) {
            b->outgoing = false;
        }
        mutex_release(mutex);
    }
}



void thread2(struct data *d) //@ : thread_run_joinable
{
    struct barrier *barrier = d->barrier;
    
    barrier(barrier);
    
    int m = 0;
    while (m < 30)
    {
        {
        }
        
        barrier(barrier);
        
        {
        }
        
        barrier(barrier);
        
        {
        }
    }
    
    barrier(barrier);
    
}
