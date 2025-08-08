

static int counter = 0;

struct shared {
    struct mutex *mtx;
};


void worker(struct shared *data) //@ : thread_run_joinable
{
    struct shared *s = data;
    mutex_acquire(s->mtx);
    
    int tmp = counter;
    if (tmp == INT_MAX) {
        abort();
    }
    counter = tmp + 1;
    
    mutex_release(s->mtx);
}

void run_workers() //@ : thread_run
{
    struct shared *s = malloc(sizeof(struct shared));
    if (s == 0) abort();
    s->mtx = create_mutex();
    
    for (int i = 0; i < NUM; i++)
    {
        struct thread *t = thread_start_joinable(worker, s);
        thread_join(t);
    }
    
    mutex_dispose(s->mtx);
    free(s);
}
