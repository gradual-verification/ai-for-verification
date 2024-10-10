#include "stdlib.h"

struct account
{
    int balance;
};

/*@


lemma void create_account_spec()
    requires true;
    ensures \result != NULL;

lemma void account_deposit_spec(struct account *myAccount, int amount)
    requires myAccount != NULL;
    ensures myAccount->balance == \old(myAccount->balance) + amount;

lemma void account_get_balance_spec(struct account *myAccount)
    requires myAccount != NULL;
    ensures true;

lemma void account_set_balance_spec(struct account *myAccount, int newBalance)
    requires myAccount != NULL;
    ensures myAccount->balance == newBalance;

lemma void account_dispose_spec(struct account *myAccount)
    requires myAccount != NULL;
    ensures true;

*/

struct account *create_account()
    //@ requires true;
    //@ ensures \result != NULL;
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
    //@ requires myAccount != NULL;
    //@ ensures myAccount->balance == \old(myAccount->balance) + amount;
{
    myAccount->balance += amount;
}

int account_get_balance(struct account *myAccount)
    //@ requires myAccount != NULL;
    //@ ensures true;
{
    int result = myAccount->balance;
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
    //@ requires myAccount != NULL;
    //@ ensures myAccount->balance == newBalance;
{
    myAccount->balance = newBalance;
}

void account_dispose(struct account *myAccount)
    //@ requires myAccount != NULL;
    //@ ensures true;
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
