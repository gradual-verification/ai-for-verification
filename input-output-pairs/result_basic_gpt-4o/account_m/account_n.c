#include "stdlib.h"
//@ #include <list.gh>

struct account
{
    int balance;
};

/*@
predicate account(struct account *acc;) =
    acc->balance |-> ?b;
@*/

/***
 * Description:
The create_account function creates a new account by dynamically allocating
memory for a struct account object.

@param none

The function initializes the balance of the account to zero. If the memory allocation
fails, the function aborts. It finally returns a pointer to the newly created account.
*/
//@ requires true;
//@ ensures account(result) &*& result != 0;
struct account *create_account()
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ close account(myAccount);
    myAccount->balance = 0;
    return myAccount;
}

/***
 * Description:
The account_set_balance function updates the balance of the given account
to the specified new balance.

@param myAccount - the account to be updated.
@param newBalance - the new balance to be set.

The function modifies the balance of the passed account to the
new balance value provided.
*/
//@ requires account(myAccount);
//@ ensures account(myAccount);
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

/***
 * Description:
The account_dispose function frees the memory allocated for the given account.

@param myAccount - the account to be deleted.

The function frees the memory allocated for the existing account.
*/
//@ requires account(myAccount);
//@ ensures true;
void account_dispose(struct account *myAccount)
{
    //@ open account(myAccount);
    free(myAccount);
}

/***
 * Description:
The main function first creates an account, then set its balance and finally dispose that account.
*/
//@ requires true;
//@ ensures true;
int main()
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}
