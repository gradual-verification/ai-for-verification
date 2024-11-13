#include "stdlib.h"

//@ predicate account_balance(struct account *acc, int balance) = acc->balance |-> balance;

struct account {
    int balance;
};

struct account *create_account()
//@ requires true;
//@ ensures account_balance(result, 0) &*& result != 0;
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0) {
        abort();
    }
    myAccount->balance = 0;
    //@ close account_balance(myAccount, 0);
    return myAccount;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
    //@ open account_balance(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account_balance(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)
//@ requires account_balance(myAccount, _);
//@ ensures true;
{
    //@ open account_balance(myAccount, _);
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
