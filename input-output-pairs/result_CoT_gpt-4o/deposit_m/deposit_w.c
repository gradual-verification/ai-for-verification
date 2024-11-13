#include "stdlib.h"

// Predicate to represent the account balance
//@ predicate account_balance(struct account *acc, int balance) = acc->balance |-> balance;

// Definition of the account structure
struct account
{
    int balance;
};

// Function to create a new account
struct account *create_account()
//@ requires true;
//@ ensures account_balance(result, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    //@ close account_balance(myAccount, 0);
    return myAccount;
}

// Function to deposit an amount into the account
void account_deposit(struct account *myAccount, int amount)
//@ requires account_balance(myAccount, ?theBalance) &*& 0 <= amount;
//@ ensures account_balance(myAccount, theBalance + amount);
{
    //@ open account_balance(myAccount, theBalance);
    myAccount->balance += amount;
    //@ close account_balance(myAccount, theBalance + amount);
}

// Function to get the balance from an account
int account_get_balance(struct account *myAccount)
//@ requires account_balance(myAccount, ?balance);
//@ ensures account_balance(myAccount, balance) &*& result == balance;
{
    //@ open account_balance(myAccount, balance);
    int result = myAccount->balance;
    //@ close account_balance(myAccount, balance);
    return result;
}

// Function to set the balance of an account
void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
    //@ open account_balance(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account_balance(myAccount, newBalance);
}

// Function to dispose of an account
void account_dispose(struct account *myAccount)
//@ requires account_balance(myAccount, _);
//@ ensures true;
{
    //@ open account_balance(myAccount, _);
    free(myAccount);
}

// Main function to demonstrate the use of account functions
int main()
//@ requires true;
//@ ensures true;
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}
