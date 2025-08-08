
struct thread;




typedef void thread_run/*@(predicate(void *) pre, predicate() post)@*/(void *data);


struct thread *thread_start(void *run, void *data)
{
    struct thread *result = malloc(sizeof(struct thread));
    if (result == 0) abort();
    
    
    
    
    
    return result;
}
