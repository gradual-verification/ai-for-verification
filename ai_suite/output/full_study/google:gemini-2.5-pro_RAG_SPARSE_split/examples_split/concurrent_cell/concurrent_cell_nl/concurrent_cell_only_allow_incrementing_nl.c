#include "threading.h"
#include "stdlib.h"
#include "assert.h"

/*@

box_class monotonic_cell_box(int value) {
    invariant true;

    action read();
        requires true;
        ensures value == old_value;

    action write(int new_value);
        requires new_value >= value;
        ensures value == new_value;

    handle_predicate client(int last_read_value) {
        invariant last_read_value <= value;

        preserved_by read() {
            // last_read_value <= old_value && old_value == value
            // ==> last_read_value <= value
        }

        preserved_by write(new_value) {
            // last_read_value <= old_value && old_value <= new_value
            // ==> last_read_value <= new_value
        }
    }
}

predicate_ctor cell_inv(struct cell *c, box box_id)() =
    c->x |-> ?v &*&
    monotonic_cell_box(box_id, v);

predicate cell_client(struct cell *c; handle h, int last_read_value) =
    c->mutex |-> ?m &*&
    malloc_block_cell(c) &*&
    exists<box>(?box_id) &*&
    [1/2]mutex(m, cell_inv(c, box_id)) &*&
    client(h, box_id, last_read_value);

@*/

struct cell {
  int x;
  struct mutex* mutex;
};


/*get function
-param: struct cell* c
-description: This get function retrieves the current value of the `x` field in the given cell structure in a thread-safe manner (using mutex). 

Other operations can be finished concurrently during this operation, so this function makes sure that
the old trace is the prefix of the new trace. 

It returns the value of `x`.
*/
int get(struct cell* c)
    //@ requires cell_client(c, ?h, ?last_read_value);
    //@ ensures cell_client(c, h, result) &*& result >= last_read_value;
{
    //@ open cell_client(c, h, last_read_value);
    //@ assert exists<box>(?box_id);

    int res;
    mutex_acquire(c->mutex);
    //@ open cell_inv(c, box_id)();
    //@ open c->x |-> ?v;

    /*@
    consuming_box_predicate monotonic_cell_box(box_id, v)
    consuming_handle_predicate client(h, last_read_value)
    perform_action read() {}
    producing_box_predicate monotonic_cell_box(v)
    producing_handle_predicate client(h, v);
    @*/

    res = c->x;

    //@ assert v >= last_read_value;

    //@ close cell_inv(c, box_id)();
    mutex_release(c->mutex);

    //@ close cell_client(c, h, res);
    return res;
}


// TODO: make this function pass the verification
/*only_allow_incrementing function
-param: struct cell* c
-description: This function checks that the value of the `x` field in the given cell structure
can only be incremented, not decremented or changed in any other way.

In the source code, it uses an assert statement to check whether the value is incremented only.
*/
void only_allow_incrementing(struct cell* c)
    //@ requires cell_client(c, ?h, ?v_init);
    //@ ensures cell_client(c, h, _);
{
  int x1 = get(c);
  //@ assert cell_client(c, h, x1) &*& x1 >= v_init;
  int x2 = get(c);
  //@ assert cell_client(c, h, x2) &*& x2 >= x1;
  assert x1 <= x2;
}