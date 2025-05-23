#include "stdlib.h"

struct account
{
    int balance;
};

/***
 * Description:
The create_account function creates a new account.

The function makes sure that the returned value is an account whose balance is zero.
*/
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

/***
 * Description:
The account_get_balance function retrieves the balance of the given account.

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
The account_set_balance function modifies the balance of a given 
account to a new specified balance value. 

@param myAccount - pointer to the existing account object.
@param newBalance - the amount to be set as the new balance.

The function ensures that the balance of the account is updated to the 
new specified balance.
*/
void account_set_balance(struct account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

/***
 * Description:
The account_deposit function is used to deposit a specified 
amount (not less than 0) into an existing account. 

@param myAccount - pointer to the existing account object.
@param amount - the specific amount to be deposited.

The function adds the deposited amount to the account balance and 
updates the account balance accordingly.
*/
void account_deposit(struct account *myAccount, int amount)
{
    myAccount->balance += amount;
}

/***
 * Description:
The account_dispose function is used to deallocate the memory allocated 
for an account object once it is no longer needed.

@param myAccount - pointer to the existing account that needs to be disposed.

The function ensures that the account is freed.
*/
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}

/***
 * Description:
The main function creates an account, sets its balance and then deposits to it.
Later, the function gets the new balance of the account and asserts its value.
Finally, the account is disposed.
*/
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
