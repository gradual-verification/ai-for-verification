
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


struct barrier *create_barrier(int n)
{
    struct barrier *b = malloc(sizeof(struct barrier));
    if (b == 0) abort();
    b->n = n;
    b->k = 0;
    b->outgoing = false;
    struct mutex *mutex = create_mutex();
    b->mutex = mutex;
    return b;
}


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


void barrier_dispose(struct barrier *b)
{
    mutex_dispose(b->mutex);
    free(b);
}


void thread1(struct data *d)
{
    struct barrier *b = d->barrier;
    
    barrier(b);

    int N = 0;
    while (N < 30)
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y1 = a1 + 2 * a2;
        
        barrier(b);
        
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x1 = a1 + 2 * a2;
        N = N + 1;
        d->i = N;
        
        barrier(b);
        
        barrier(b);
    }
    
    barrier(b);
    d->i = 0;
}


void thread2(struct data *d)
{
    struct barrier *b = d->barrier;
    
    barrier(b);
    
    int m = 0;
    while (m < 30)
    {
        int a1 = d->x1;
        int a2 = d->x2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->y2 = a1 + 3 * a2;
        
        barrier(b);
        
        a1 = d->y1;
        a2 = d->y2;
        if (a1 < 0 || a1 > 1000 || a2 < 0 || a2 > 1000) {abort();}
        d->x2 = a1 + 3 * a2;
        
        barrier(b);
        
        m = d->i;
        barrier(b);
    }
    
    barrier(b);
}


int main()
{
    struct data *d = calloc(1, sizeof(struct data));
    if (d == 0) abort();
    
    struct barrier *b = create_barrier(2);
    d->barrier = b;

    struct thread *t1 = thread_start_joinable(thread1, d);
    struct thread *t2 = thread_start_joinable(thread2, d);
    
    thread_join(t1);
    thread_join(t2);
    
    barrier_dispose(d->barrier);
  
    free(d);
    return 0;
}
