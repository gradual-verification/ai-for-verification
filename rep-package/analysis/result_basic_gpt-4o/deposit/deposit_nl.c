#include "stdlib.h"
#include "stdbool.h"

struct account
{
    int balance;
};

// Predicate for account
/*@
predicate account(struct account *acc; int balance) =
    acc != 0 &*& acc->balance |-> balance;
@*/


struct account *create_account()
    //@ requires true;
    //@ ensures account(result, 0) &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}


void account_deposit(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?oldBalance) &*& oldBalance + amount <= INT_MAX &*& oldBalance + amount >= INT_MIN;
    //@ ensures account(myAccount, oldBalance + amount);
{
    myAccount->balance += amount;
}


int account_get_balance(struct account *myAccount)
    //@ requires account(myAccount, ?balance);
    //@ ensures account(myAccount, balance) &*& result == balance;
{
    int result = myAccount->balance;
    return result;
}


void account_set_balance(struct account *myAccount, int newBalance)
    //@ requires account(myAccount, _);
    //@ ensures account(myAccount, newBalance);
{
    myAccount->balance = newBalance;
}


void account_dispose(struct account *myAccount)
    //@ requires account(myAccount, _) &*& malloc_block_account(myAccount);
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
