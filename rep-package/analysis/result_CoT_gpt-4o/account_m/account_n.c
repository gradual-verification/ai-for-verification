#include "stdlib.h"

struct account
{
    int balance;
};

/*@
predicate account(struct account *myAccount; int balance) =
    myAccount->balance |-> balance;
@*/


struct account *create_account()
//@ requires true;
//@ ensures result != 0 &*& account(result, 0) &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    
    myAccount->balance = 0;
    return myAccount;
    //@ close account(myAccount, 0);
}


void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account(myAccount, _);
//@ ensures account(myAccount, newBalance);
{
    //@ open account(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}


void account_dispose(struct account *myAccount)
//@ requires account(myAccount, _) &*& malloc_block_account(myAccount);
//@ ensures true;
{
    //@ open account(myAccount, _);
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
