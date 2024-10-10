#include "stdlib.h"

struct account
{
    int balance;
};

/*@ 
predicate account(struct account *acc;) = 
    acc != \null &*&
    malloc_block_account(acc) &*&
    acc->balance |-> _;

@*/

/*@ 
requires true;
ensures result != \null;
ensures account(result);
@*/
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}

/*@ 
requires account(acc) &*&
    acc->balance |-> _ &*&
    newBalance >= 0;
ensures account(acc) &*&
    acc->balance |-> newBalance;
@*/
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

/*@ 
requires account(acc);
ensures true;
@*/
void account_dispose(struct account *myAccount)
{
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
