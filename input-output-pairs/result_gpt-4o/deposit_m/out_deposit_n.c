#include "stdlib.h"

// The predicate that describes when we own a valid account structure
//@ predicate account(struct account *a, int balance) = a->balance |-> balance;

struct account {
    int balance;
};

/***
 * Description:
 * The create_account function creates a new account by allocating 
 * memory for it dynamically.
 *
 * @param none
 *
 * The function creates a new account and after verifying that the 
 * memory allocation was successful, it initializes the balance of 
 * the account to zero and returns a pointer to the newly created account.
 */
//@ requires true;
//@ ensures account(result, 0);
struct account *create_account() 
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0) 
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close account(myAccount, 0);
    return myAccount;
}

/***
 * Description:
 * The account_deposit function is used to deposit a specified 
 * amount into an existing account.
 *
 * @param myAccount - pointer to the existing account object.
 * @param amount - the specific amount to be deposited.
 *
 * The function adds the deposited amount to the account balance and 
 * updates the account balance accordingly.
 */
//@ requires account(myAccount, ?b);
//@ ensures account(myAccount, b + amount);
void account_deposit(struct account *myAccount, int amount) 
{
    myAccount->balance += amount;
}

/***
 * Description:
 * The account_get_balance function retrieves the balance of
 * the given account.
 *
 * @param myAccount - pointer to an existing account.
 *
 * The function returns the current balance of the account
 * and does not modify any data.
 */
//@ requires account(myAccount, ?b);
//@ ensures account(myAccount, b) &*& result == b;
int account_get_balance(struct account *myAccount) 
{
    int result = myAccount->balance;
    return result;
}

/***
 * Description:
 * The account_set_balance function modifies the balance of a given 
 * account to a new specified balance value.
 *
 * @param myAccount - pointer to the existing account object.
 * @param newBalance - the amount to be set as the new balance.
 *
 * The function ensures that the balance of the account is updated to the 
 * new specified balance.
 */
//@ requires account(myAccount, _);
//@ ensures account(myAccount, newBalance);
void account_set_balance(struct account *myAccount, int newBalance) 
{
    myAccount->balance = newBalance;
}

/***
 * Description:
 * The account_dispose function is used to deallocate the memory allocated 
 * for an account object once it is no longer needed.
 *
 * @param myAccount - pointer to the existing account that needs to be disposed.
 *
 * The function ensures that the memory allocated for the account is freed.
 */
//@ requires account(myAccount, _);
//@ ensures true;
void account_dispose(struct account *myAccount) 
{
    //@ open account(myAccount, _);
    free(myAccount);
}

/***
 * Description:
 * The main function creates an account, sets its balance and then deposits to it.
 * Later, the function gets the new balance of the account and asserts its value.
 * Finally, the account is disposed.
 */
//@ requires true;
//@ ensures true;
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
