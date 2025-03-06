#include "threading.h"
#include "stdlib.h"

struct cell {
  int x;
  struct mutex* mutex;
};

/*cell_create function
-param: none
-description: This function creates a new cell with an intialized mutex in it.

It requires that there exists a function that checks whether a trace is valid (where the empty trace is valid)
It ensures that the mutex in the cell enables that checking function to hold (if the cell is not null).

It returns a pointer to the newly created cell.
*/
struct cell* cell_create()
{
  struct cell* c = malloc(sizeof(struct cell));
  if(c == 0) return 0;
  c->x = 0;
  struct mutex* m = create_mutex();
  c->mutex = m;
  return c;
}

/*increment function
-param: struct cell* c
-description: This function increments field x in the given cell c in a thread-safe manner (using mutex).

It requires that the given cell c is valid, and there is a function to check whether incrementing on a trace is valid, 
and c has an original trace.
It ensures that the original trace is the prefix of new trace, and the new value in c->x can be calulated by executing the new trace.
*/
void increment(struct cell* c)
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MAX) {
    abort();
  }
  c->x++;
  {
  
  }
  mutex_release(c->mutex);
}

/*decrement function
-param: struct cell* c
-description: This function decrements field x in the given cell c in a thread-safe manner (using mutex).

It requires that the given cell c is valid, and there is a function to check whether decrementing on a trace is valid, 
and c has an original trace.
It ensures that the original trace is the prefix of new trace, and the new value in c->x can be calulated by executing the new trace.
*/
void decrement(struct cell* c)
{
  mutex_acquire(c->mutex);
  if (c->x == INT_MIN) {
    abort();
  }
  c->x--;
  {
    
  }
  mutex_release(c->mutex);
}

/*cas function
-param: struct cell* c, int old, int new
-description: This compare-and-swap function checks if the current value of `x` in the given cell c is equal to `old`.
If it is, the function updates `x` to `new`. This operation is thread-safe due to the use of a mutex. 

It requires that the given cell c is valid, and there is a function to check whether compare-and-swap on a trace is valid,
and c has an original trace.
It ensures that the original trace is the prefix of new trace, and the new value in c->x can be calulated by executing the new trace.

It returns the original value of `x` before the operation.
*/
int cas(struct cell* c, int old, int new)
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  if(c->x == old) {
    c->x = new;
  }
  {
    
  }
  mutex_release(c->mutex);
  return res;
}

/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

It requires that the given cell c is valid, and there is a function to check whether the trace is valid,
and c has an original trace.
It ensures that the original trace is the prefix of new trace, and the new value in c->x can be calulated by executing the new trace.

It returns the value of `x`.
*/
int get(struct cell* c)
{
  int res;
  mutex_acquire(c->mutex);
  res = c->x;
  {
  }
  mutex_release(c->mutex);
  return res;
}

/*only_allow_incrementing function
-param: struct cell* c
-description: This function checks that the value of the `x` field in the given cell structure
can only be incremented, not decremented or changed in any other way.

It requires that the given cell c is valid, and there is a function to make sure only incrementing the value is valid,
and c has an original trace. In the source code, it uses an assert statement to check whether the value is incremented only.
*/
void only_allow_incrementing(struct cell* c)
{
  int x1 = get(c);
  int x2 = get(c);
  assert x1 <= x2;
}
