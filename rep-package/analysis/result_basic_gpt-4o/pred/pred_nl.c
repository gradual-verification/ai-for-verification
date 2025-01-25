#include "stdlib.h"

/*@

predicate account(struct account *acc, int limit, int bal) =
    acc->limit |-> limit &*& acc->balance |-> bal &*& malloc_block_account(acc);

@*/

struct account
{
    int limit;
    int balance;
};


struct account *create_account(int limit)
//@ requires limit <= 0;
//@ ensures account(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    return myAccount;
    //@ close account(myAccount, limit, 0);
}


int account_get_balance(struct account *myAccount)
//@ requires account(myAccount, ?limit, ?bal);
//@ ensures account(myAccount, limit, bal) &*& result == bal;
{
    //@ open account(myAccount, limit, bal);
    int result = myAccount->balance;
    //@ close account(myAccount, limit, bal);
    return result;
}


void account_deposit(struct account *myAccount, int amount)
//@ requires account(myAccount, ?limit, ?bal) &*& 0 <= amount &*& bal + amount <= INT_MAX;
//@ ensures account(myAccount, limit, bal + amount);
{
    //@ open account(myAccount, limit, bal);
    myAccount->balance += amount;
    //@ close account(myAccount, limit, bal + amount);
}


int account_withdraw(struct account *myAccount, int amount)
//@ requires account(myAccount, ?limit, ?bal) &*& 0 <= amount &*& bal - amount >= INT_MIN &*& bal - limit >= INT_MIN;
//@ ensures account(myAccount, limit, bal - result) &*& result == (bal - amount <= limit ? bal - limit : amount);
{
    //@ open account(myAccount, limit, bal);
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    //@ close account(myAccount, limit, bal - result);
    return result;
}


void account_dispose(struct account *myAccount)
//@ requires account(myAccount, _, _);
//@ ensures true;
{
    //@ open account(myAccount, _, _);
    free(myAccount);
}


int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account(-100);
    account_deposit(myAccount, 200);
    int w1 = account_withdraw(myAccount, 50);
    assert(w1 == 50);
    int b1 = account_get_balance(myAccount);
    assert(b1 == 150);
    int w2 = account_withdraw(myAccount, 300);
    assert(w2 == 250);
    int b2 = account_get_balance(myAccount);
    assert(b2 == -100);
    account_dispose(myAccount);
    return 0;
}
