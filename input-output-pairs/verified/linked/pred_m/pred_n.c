#include "stdlib.h"

struct account
{
    int limit;
    int balance;
};

/***
 * Description:
The create_account function creates a new account with the specified limit.

@param limit - represents the limit of the new account, which should be no greater than 0.

The function allocates memory for a new account struct, sets
the limit to the provided value, initializes the balance to 0,
and then returns a pointer to the created account.
*/
struct account *create_account(int limit)
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

/***
 * Description:
The account_get_balance function retrieves the balance of
the given account.

@param myAccount - pointer to an existing account.

The function returns the current balance of the account
and does not modify any data.
*/
int account_get_balance(struct account *myAccount)
{
    int result = myAccount->balance;
    return result;
}

/***
 * Description:
The account_deposit function adds a specified amount
to the balance of the given account.

@param myAccount - pointer to an existing account.
@param amount - amount to be deposited

The function increases the account's balance by the specified amount, 
and it need to make sure the increased balance doesn't overflow.
*/
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
}

/***
 * Description:
The account_withdraw function withdraws a specified amount
from the account's balance.

@param myAccount - pointer to an existing account.
@param amount - amount to be withdrawn

The function calculates the actual amount to withdraw based on
the account's current balance and limit such that the new balance is no less than limit.
It then updates the balance accordingly, and finally returns the withdrawn amount.
*/
int account_withdraw(struct account *myAccount, int amount)
{
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    return result;
}

/***
 * Description:
The account_dispose function releases the memory allocated for the given account.

@param myAccount - pointer to an existing account to be deleted.

The function frees the memory associated with the account,
allowing it to be deallocated.
*/
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

/***
 * Description:
The main function first creates an account with a negative limit, 
then does some deposits and withdraws and validates the balance is correct,
and finally dispose the account.
*/
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
