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
struct bst_node *bst_insert(struct bst_node *node, int value)
    //@ requires bst(node, ?min, ?max) &*& min < value &*& value < max;
    //@ ensures bst(result, min, max);
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        return new_node;
    } else {
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {   
        }

        return node;
    }
}

// Function to compute the sum of the values in the BST
int bst_sum(struct bst_node *node)
    //@ requires bst(node, ?min, ?max);
    //@ ensures result == sum_values(node) &*& bst(node, min, max);
{
    if (node == 0) {
        return 0;
    } else {
        //@ open bst(node, min, max);
        int left_sum = bst_sum(node->left);
        int right_sum = bst_sum(node->right);
        int total = left_sum + right_sum + node->value;
        //@ close bst(node, min, max);
        return total;
    }
}

// Thread data structure for concurrent sum computation
struct sum_data {
    struct thread *thread;
    struct bst_node *tree;
    int sum;
};

/*@ 
predicate_family_instance thread_run_pre(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& bst(tree, _, _);
predicate_family_instance thread_run_post(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& bst(tree, _, _) &*& data->sum |-> ?sum;
@*/

// Thread function to compute the sum of the BST
void summator(struct sum_data *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(summator)(data, ?info);
    //@ ensures thread_run_post(summator)(data, info);
{
    //@ open thread_run_pre(summator)(data, info);
    int sum = bst_sum(data->tree);
    data->sum = sum;
    //@ close thread_run_post(summator)(data, info);
}

// Function to start a sum thread
struct sum_data *start_sum_thread(struct bst_node *tree)
    //@ requires bst(tree, _, _);
    //@ ensures result->thread |-> ?t &*& thread(t, summator, result, _);
{
    struct sum_data *data = malloc(sizeof(struct sum_data));
    struct thread *t = 0;
    if (data == 0) abort();
    data->tree = tree;
    //@ close thread_run_pre(summator)(data, unit);
    t = thread_start_joinable(summator, data);
    data->thread = t;
    return data;
}

// Function to join a sum thread
int join_sum_thread(struct sum_data *data)
    //@ requires data->thread |-> ?t &*& thread(t, summator, data, _);
    //@ ensures true;
{
    thread_join(data->thread);
    //@ open thread_run_post(summator)(data, _);
    return data->sum;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct bst_node *tree = 0;
    tree = bst_insert(tree, 10);
    tree = bst_insert(tree, 5);
    tree = bst_insert(tree, 15);
    
    struct sum_data *sumData = start_sum_thread(tree);
    int total_sum = join_sum_thread(sumData);
    
    printf("Total sum: %i\n", total_sum);
    
    return 0;
}