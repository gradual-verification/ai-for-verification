

typedef void thread_run (void *data);

struct thread;


typedef void thread_run_with_contract(void *data);

struct thread *thread_start(thread_run_with_contract *run, void *data);

void thread_join(struct thread *thread);
