#include "stdlib.h"
#include "stdbool.h"
#include "stdio.h"
#include "threading.h"

struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};

/*@ 
predicate bst(struct bst_node *node, int min, int max) =
    node == 0 ?
        true
    :
        malloc_block_bst_node(node) &*&
        node->value |-> ?v &*& min < v &*& v < max &*&
        node->left |-> ?left &*& node->right |-> ?right &*&
        bst(left, min, v) &*& bst(right, v, max);
@*/

// TODO: make this function pass the verification
struct bst_node *bst_create()
    //@ requires true;
    //@ ensures bst(result, INT_MIN, INT_MAX);
{
    struct bst_node *node = malloc(sizeof(struct bst_node));
    if (node == 0) abort();
    node->left = 0;
    node->right = 0;
    node->value = 0; // Initialize with a default value
    return node;
}

// Function to compute the factorial of a number
int fac(int x)
    //@ requires true;
    //@ ensures x >= 0 ? result == (x == 0 ? 1 : x * fac(x - 1)) : false;
{
    int result = 1;
    while (x > 1)
        //@ invariant result == (x == 0 ? 1 : x * fac(x - 1));
    {
        result = result * x;
        x = x - 1;
    }
    return result;
}

// Function to create a binary search tree
struct bst_node *make_tree(int depth)
    //@ requires true;
    //@ ensures bst(result, INT_MIN, INT_MAX);
{
    if (depth == 0) {
        return 0;
    } else {
        struct bst_node *left = make_tree(depth - 1);
        struct bst_node *right = make_tree(depth - 1);
        int value = rand() % 2000; // Random value for the node
        struct bst_node *t = malloc(sizeof(struct bst_node));
        if (t == 0) abort();
        t->left = left;
        t->right = right;
        t->value = value;
        return t;
    }
}

// Function to compute the sum of factorials in the BST
int tree_compute_sum_facs(struct bst_node *tree)
    //@ requires bst(tree, INT_MIN, INT_MAX);
    //@ ensures bst(tree, INT_MIN, INT_MAX);
{
    if (tree == 0) {
        return 0;
    } else {
        //@ open bst(tree, INT_MIN, INT_MAX);
        int leftSum = tree_compute_sum_facs(tree->left);
        int rightSum = tree_compute_sum_facs(tree->right);
        int f = fac(tree->value);
        return leftSum + rightSum + f;
        //@ close bst(tree, INT_MIN, INT_MAX);
    }
}

// Struct to hold data for threading
struct sum_data {
    struct thread *thread;
    struct bst_node *tree;
    int sum;
};

/*@ 
predicate_family_instance thread_run_pre(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& bst(tree, INT_MIN, INT_MAX) &*& data->sum |-> _;
predicate_family_instance thread_run_post(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& bst(tree, INT_MIN, INT_MAX) &*& data->sum |-> ?sum;
@*/

// Thread function to compute sum of factorials
void summator(struct sum_data *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(summator)(data, ?info);
    //@ ensures thread_run_post(summator)(data, info);
{
    //@ open thread_run_pre(summator)(data, info);
    int sum = tree_compute_sum_facs(data->tree);
    data->sum = sum;
    //@ close thread_run_post(summator)(data, info);
}

// Function to start a thread for summation
struct sum_data *start_sum_thread(struct bst_node *tree)
    //@ requires bst(tree, INT_MIN, INT_MAX);
    //@ ensures result->thread |-> ?t &*& thread(t, summator, result, _);
{
    struct sum_data *data = malloc(sizeof(struct sum_data));
    struct thread *t = 0;
    if (data == 0) abort();
    data->tree = tree;
    data->sum = 0; // Initialize sum
    //@ close thread_run_pre(summator)(data, unit);
    t = thread_start_joinable(summator, data);
    data->thread = t;
    return data;
}

// Function to join a thread and get the result
int join_sum_thread(struct sum_data *data)
    //@ requires data->thread |-> ?t &*& thread(t, summator, data, _);
    //@ ensures true;
{
    thread_join(data->thread);
    //@ open thread_run_post(summator)(data, _);
    return data->sum;
    //@ leak data->tree |-> ?tree &*& bst(tree, INT_MIN, INT_MAX) &*& data->sum |-> _ &*& data->thread |-> _;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct bst_node *tree = make_tree(22);
    struct sum_data *leftData = start_sum_thread(tree->left);
    struct sum_data *rightData = start_sum_thread(tree->right);
    int sumLeft = join_sum_thread(leftData);
    int sumRight = join_sum_thread(rightData);
    int f = fac(tree->value);
    printf("%i", sumLeft + sumRight + f);
    return 0;
}