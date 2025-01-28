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

struct account *create_account()
//@ requires true;
//@ ensures account(result) &*& result != 0 &*& malloc_block_account(result);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    // @ close account(myAccount);
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

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account(myAccount);
//@ ensures account(myAccount);
{
    myAccount->balance = newBalance;
}

/***
 * Description:
The account_dispose function frees the memory allocated for the given account.

@param myAccount - the account to be deleted.

The function frees the memory allocated for the existing account.
*/

void account_dispose(struct account *myAccount)
//@ requires account(myAccount) &*& malloc_block_account(myAccount);
//@ ensures true;
{
    //@ open account(myAccount);
    free(myAccount);
}

/***
 * Description:
The main function first creates an account, then set its balance and finally dispose that account.
*/

int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_dispose(myAccount);
    return 0;
}
