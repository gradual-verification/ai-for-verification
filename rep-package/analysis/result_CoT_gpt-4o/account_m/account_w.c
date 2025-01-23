#include "stdlib.h"

// Predicate representing the state of an account with a known balance.
//predicate account_balance(struct account *a; int b) =
//    a->balance |-> b;

// Structure representing an account.
struct account {
    int balance;
};

// Create an account with an initial balance of 0.

struct account *create_account() 
//@ requires true;
//@ ensures account_balance(result, 0) &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close account_balance(myAccount, 0);
    return myAccount;
}

// Set the balance of the given account.

void account_set_balance(struct account *myAccount, int newBalance) 
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
    //@ open account_balance(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account_balance(myAccount, newBalance);
}

// Dispose of an account, releasing its memory.

void account_dispose(struct account *myAccount) 
//@ requires account_balance(myAccount, _) &*& malloc_block_account(myAccount);
//@ ensures true;
{
    //@ open account_balance(myAccount, _);
    free(myAccount);
}

// Main function that demonstrates creating, modifying, and disposing of an account.

int main() 
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}
