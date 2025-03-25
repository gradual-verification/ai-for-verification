#include "stdlib.h"

struct account {
    int balance;
};

struct account *create_account()
    //@ requires true;
    //@ ensures result->balance |-> 0;
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0) { abort(); }
    myAccount->balance = 0;
    return myAccount;
}

void account_set_balance(struct account *myAccount, int newBalance)
    //@ requires myAccount->balance |-> _;
    //@ ensures myAccount->balance |-> newBalance;
{
    myAccount->balance = newBalance;
}

void account_dispose(struct account *myAccount)
    //@ requires myAccount->balance |-> _;
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
    account_dispose(myAccount);
    return 0;
}