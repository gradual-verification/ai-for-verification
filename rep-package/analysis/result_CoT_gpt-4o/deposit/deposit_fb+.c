#include "stdlib.h"

// @ predicate account_balance(struct account* a, int b) = a->balance |-> b;
// @ predicate malloc_block_account(struct account* a) = malloc_block(a, sizeof(struct account));

struct account {
    int balance;
};

struct account *create_account()
//@ requires true;
//@ ensures account_balance(result, 0) &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0) {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
/*@ requires account_balance(myAccount, ?theBalance) &*& 0 <= amount 
      &*& theBalance + amount <= INT_MAX &*& theBalance + amount >= INT_MIN; @*/
//@ ensures account_balance(myAccount, theBalance + amount);
{
    myAccount->balance += amount;
}

int account_get_balance(struct account *myAccount)
//@ requires account_balance(myAccount, ?balance);
//@ ensures account_balance(myAccount, balance) &*& result == balance;
{
    int result = myAccount->balance;
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
    myAccount->balance = newBalance;
}

void account_dispose(struct account *myAccount)
//@ requires account_balance(myAccount, _) &*& malloc_block_account(myAccount);
//@ ensures true;
{
    free(myAccount);
}

int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}
