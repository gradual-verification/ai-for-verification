#include "stdlib.h"
#include "assert.h"

/*@
predicate account(struct account* acc; int limit, int balance) =
    acc != 0 &*&
    malloc_block_account(acc) &*&
    acc->limit |-> limit &*& acc->balance |-> balance;
@*/

struct account
{
    int limit;
    int balance;
};

/*@
requires limit <= 0;
ensures account(result, limit, 0);
@*/
struct account *create_account(int limit)
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    //@ close account(myAccount, limit, 0);
    return myAccount;
}

/*@
requires account(myAccount, ?limit, ?balance);
ensures account(myAccount, limit, balance) &*& result == balance;
@*/
int account_get_balance(struct account *myAccount)
{
    //@ open account(myAccount, ?limit, ?balance);
    int result = myAccount->balance;
    //@ close account(myAccount, limit, balance);
    return result;
}

/*@
requires account(myAccount, ?limit, ?balance);
ensures account(myAccount, limit, balance + amount);
@*/
void account_deposit(struct account *myAccount, int amount)
{
    //@ open account(myAccount, ?limit, ?balance);
    myAccount->balance += amount;
    //@ close account(myAccount, limit, balance + amount);
}

/*@
requires account(myAccount, ?limit, ?balance);
ensures account(myAccount, limit, balance - result) &*&
        result == (balance - amount < limit ? balance - limit : amount);
@*/
int account_withdraw(struct account *myAccount, int amount)
{
    //@ open account(myAccount, ?limit, ?balance);
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    //@ close account(myAccount, limit, balance - result);
    return result;
}

/*@
requires account(myAccount, ?limit, ?balance);
ensures true;
@*/
void account_dispose(struct account *myAccount)
{
    //@ open account(myAccount, ?limit, ?balance);
    free(myAccount);
}

/*@
requires true;
ensures true;
@*/
int main()
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
