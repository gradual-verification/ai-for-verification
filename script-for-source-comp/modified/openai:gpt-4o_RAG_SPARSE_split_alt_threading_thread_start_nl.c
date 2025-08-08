

typedef void thread_run(void *data);

struct thread;

struct thread *thread_start(void *run, void *data);

void thread_join(struct thread *thread);

struct thread *thread_start(void *run, void *data) {
    struct thread *t = malloc(sizeof(struct thread));
    if (t == 0) abort();
    return t;
}

void thread_join(struct thread *thread) {
}
