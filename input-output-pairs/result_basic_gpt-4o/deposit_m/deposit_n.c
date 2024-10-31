#include "stdlib.h"
#include "stdbool.h"

struct account
{
    int balance;
};

// Predicate for account
predicate account(struct account *acc; int balance) =
    acc != 0 &*& acc->balance |-> balance;

/*@
  ensures result != 0;
  ensures account(result, 0);
  @*/
struct account *create_account()
    //@ requires true;
    //@ ensures account(result, 0);
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
  requires account(myAccount, ?oldBalance);
  ensures account(myAccount, oldBalance + amount);
  @*/
void account_deposit(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?oldBalance);
    //@ ensures account(myAccount, oldBalance + amount);
{
    myAccount->balance += amount;
}

/*@
  requires account(myAccount, ?balance);
  ensures account(myAccount, balance) &*& result == balance;
  @*/
int account_get_balance(struct account *myAccount)
    //@ requires account(myAccount, ?balance);
    //@ ensures account(myAccount, balance) &*& result == balance;
{
    int result = myAccount->balance;
    return result;
}

/*@
  requires account(myAccount, _);
  ensures account(myAccount, newBalance);
  @*/
void account_set_balance(struct account *myAccount, int newBalance)
    //@ requires account(myAccount, _);
    //@ ensures account(myAccount, newBalance);
{
    myAccount->balance = newBalance;
}

/*@
  requires account(myAccount, _);
  ensures true;
  @*/
void account_dispose(struct account *myAccount)
    //@ requires account(myAccount, _);
    //@ ensures true;
{
    free(myAccount);
}

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
