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

The function makes sure that the returned value is an account with its limit set to the provided value
and balance set to 0. 
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
and does not modify the account.
*/
int account_get_balance(struct account *myAccount)
{
    int result = myAccount->balance;
    return result;
}

/***
 * Description:
The account_deposit function adds a specified amount (not less than 0)
to the balance of the given account.

@param myAccount - pointer to an existing account.
@param amount - amount to be deposited

The function increases the account's balance by the specified amount.
*/
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
}

/***
 * Description:
The account_withdraw function withdraws a specified amount (not less than 0)
from the account's balance.

@param myAccount - pointer to an existing account.
@param amount - amount to be withdrawn

The function makes sure that if balance - amount is no less than limit, then the withdrawal value is the given amount; 
Otherwise, the withdrawal value is balance - limit.
Also, it will return the withdrawal value.
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
The main function test the operations of account. 
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
