
struct thread;




typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);


struct thread *thread_start_joinable(void *run, void *data)
{
    return 0;
}

void thread_join(struct thread *thread)
{
}

