#include "stdlib.h"

struct account
{
    int balance;
};

/*@
predicate account(struct account *myAccount; int balance) =
    myAccount->balance |-> balance;
@*/

/*@
requires true;
ensures result != 0 &*& account(result, 0);
@*/
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ close account(myAccount, 0);
    myAccount->balance = 0;
    return myAccount;
}

/*@
requires account(myAccount, _);
ensures account(myAccount, newBalance);
@*/
void account_set_balance(struct account *myAccount, int newBalance)
{
    //@ open account(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account(myAccount, newBalance);
}

/*@
requires account(myAccount, _);
ensures true;
@*/
void account_dispose(struct account *myAccount)
{
    //@ open account(myAccount, _);
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
    account_dispose(myAccount);
    return 0;
}
