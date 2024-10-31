#include "stdlib.h"

//@ predicate accountp(struct account *acc; int balance) = acc->balance |-> balance;

struct account
{
    int balance;
};

/*@
requires true;
ensures accountp(result, 0);
@*/
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close accountp(myAccount, 0);
    return myAccount;
}

/*@
requires accountp(myAccount, ?balance);
ensures accountp(myAccount, balance + amount);
@*/
void account_deposit(struct account *myAccount, int amount)
{
    //@ open accountp(myAccount, balance);
    myAccount->balance += amount;
    //@ close accountp(myAccount, balance + amount);
}

/*@
requires accountp(myAccount, ?balance);
ensures accountp(myAccount, balance) &*& result == balance;
@*/
int account_get_balance(struct account *myAccount)
{
    //@ open accountp(myAccount, balance);
    int result = myAccount->balance;
    //@ close accountp(myAccount, balance);
    return result;
}

/*@
requires accountp(myAccount, _);
ensures accountp(myAccount, newBalance);
@*/
void account_set_balance(struct account *myAccount, int newBalance)
{
    //@ open accountp(myAccount, _);
    myAccount->balance = newBalance;
    //@ close accountp(myAccount, newBalance);
}

/*@
requires accountp(myAccount, _);
ensures true;
@*/
void account_dispose(struct account *myAccount)
{
    //@ open accountp(myAccount, _);
    free(myAccount);
}

/*@
requires true;
ensures true;
@*/
int main()
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}
