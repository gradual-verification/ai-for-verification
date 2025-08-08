
struct rwlock {
    struct mutex *mutex;
    int readers;
};


struct rwlock *rwlock_init()
{
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();
    l->readers = 0;
    struct mutex *m = create_mutex();
    l->mutex = m;
    return l;
}

void reader(struct rwlock *l) //@ : thread_run
{
    mutex_acquire(l->mutex);

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;
    mutex_release(l->mutex);


    mutex_acquire(l->mutex);
    if (l->readers == 0) {
        abort();
    }
    l->readers--;
    mutex_release(l->mutex);
}

void writer(struct rwlock *l) //@ : thread_run
{
    for (;;)
    {
        mutex_acquire(l->mutex);
        if (l->readers == 0) {
            break;
        }
        mutex_release(l->mutex);
    }


    mutex_release(l->mutex);
}

int main() //@ : main
{
    struct rwlock *l = rwlock_init();

    thread_start(reader, l);
    
    thread_start(writer, l);

    return 0;
}
