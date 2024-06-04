#include "stdlib.h"
struct account
{
    int balance;
};

/***
 * Description:
The function `create_account` creates a new account by allocating 
memory for it dynamically.

@param none

The function creates a new account and after verifying that the 
memory allocation was successful, it initializes the balance of 
the account to zero and returns a pointer to the newly created 
account.

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
The function `account_deposit` is used to deposit a specified 
amount into an existing account. 

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
The function `account_set_balance` modifies the balance of a given 
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
The function `account_dispose` is used to deallocate the memory allocated 
for an account object once it is no longer needed.

@param myAccount - pointer to the existing account that needs to be disposed.

The function ensures that the memory allocated for the account is freed.
*/
void account_dispose(struct account *myAccount)
{
    free(myAccount);
}
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
