// atomic_load function
// param: c: pointer to the cell
// description: atomically load and return the value of the cell.
//
// It ensures that the old trace is the prefix of current trace.

/*@
// Define a trace predicate to track the history of operations
predicate trace(list<int> history);

// Define a cell predicate to represent the integer cell with its value and history
predicate cell(int* c, int value; list<int> history) =
    *c |-> value &*& trace(history);
@*/

int atomic_load(int* c)
//@ requires cell(c, ?value, ?old_history);
//@ ensures cell(c, value, ?new_history) &*& prefix(old_history, new_history) == true &*& result == value;
{
    //@ open cell(c, value, old_history);
    int result = *c;
    //@ close cell(c, value, cons(value, old_history));
    return result;
}

/*@
// Define a prefix predicate to check if one list is a prefix of another
fixpoint bool prefix<t>(list<t> xs, list<t> ys) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): 
            switch (ys) {
                case nil: return false;
                case cons(y, ys0): return x == y && prefix(xs0, ys0);
            }
    }
}
@*/