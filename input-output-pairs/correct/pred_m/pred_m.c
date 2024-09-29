#include "stdlib.h"

struct account
{
    int limit;
    int balance;
};

/*@
predicate account_pred(struct account *myAccount, int theLimit, int theBalance) =
myAccount->limit |-> theLimit &*& myAccount->balance |-> theBalance
&*& malloc_block_account(myAccount);
@*/

struct account *create_account(int limit)
//@ requires limit <= 0;
//@ ensures account_pred(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    return myAccount;
}

int account_get_balance(struct account *myAccount)
//@ requires account_pred(myAccount, ?limit, ?balance);
//@ ensures account_pred(myAccount, limit, balance) &*& result == balance;
{
    int result = myAccount->balance;
    return result;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account_pred(myAccount, ?limit, ?balance) &*& 0 <= amount &*& balance + amount <= INT_MAX;
//@ ensures account_pred(myAccount, limit, balance + amount);
{
    myAccount->balance += amount;
}

int account_withdraw(struct account *myAccount, int amount)
//@ requires account_pred(myAccount, ?limit, ?balance) &*& 0 <= amount &*& balance - amount >= INT_MIN &*& balance - limit >= INT_MIN;
/*@ ensures account_pred(myAccount, limit, balance - result)
&*& result == (balance - amount < limit ? balance - limit : amount); @*/
{
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    return result;
}

void account_dispose(struct account *myAccount)
//@ requires account_pred(myAccount, _, _);
//@ ensures true;
{
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
