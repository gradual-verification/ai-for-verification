#include "stdlib.h"

/*@

predicate account(struct account *a; int limit, int balance) =
    a->limit |-> limit &*& a->balance |-> balance &*& malloc_block_account(a);

@*/

struct account
{
    int limit;
    int balance;
};

/***
 * Description:
 * The create_account function creates a new account with the specified limit.
 * @param limit - represents the limit of the new account, which should be no greater than 0.
 * The function allocates memory for a new account struct, sets
 * the limit to the provided value, initializes the balance to 0,
 * and then returns a pointer to the created account.
 */
struct account *create_account(int limit)
    //@ requires limit <= 0;
    //@ ensures account(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    //@ assume(myAccount != 0);
    //@ malloc_block_account(myAccount);
    //@ close account(myAccount, _, _);
    myAccount->limit = limit;
    myAccount->balance = 0;
    //@ close account(myAccount, limit, 0);
    return myAccount;
}

/***
 * Description:
 * The account_get_balance function retrieves the balance of
 * the given account.
 * @param myAccount - pointer to an existing account.
 * The function returns the current balance of the account
 * and does not modify any data.
 */
int account_get_balance(struct account *myAccount)
    //@ requires account(myAccount, ?limit, ?balance);
    //@ ensures account(myAccount, limit, balance) &*& result == balance;
{
    //@ open account(myAccount, limit, balance);
    int result = myAccount->balance;
    //@ close account(myAccount, limit, balance);
    return result;
}

/***
 * Description:
 * The account_deposit function adds a specified amount
 * to the balance of the given account.
 * @param myAccount - pointer to an existing account.
 * @param amount - amount to be deposited
 * The function increases the account's balance by the specified amount.
 */
void account_deposit(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance) &*& amount >= 0;
    //@ ensures account(myAccount, limit, balance + amount);
{
    //@ open account(myAccount, limit, balance);
    myAccount->balance += amount;
    //@ close account(myAccount, limit, balance + amount);
}

/***
 * Description:
 * The account_withdraw function withdraws a specified amount
 * from the account's balance.
 * @param myAccount - pointer to an existing account.
 * @param amount - amount to be withdrawn
 * The function calculates the actual amount to withdraw based on
 * the account's current balance and limit such that the new balance is no less than limit.
 * It then updates the balance accordingly, and finally returns the withdrawn amount.
 */
int account_withdraw(struct account *myAccount, int amount)
    //@ requires account(myAccount, ?limit, ?balance) &*& amount >= 0;
    /*@
    ensures account(myAccount, limit, balance - result) &*&
            result == (balance - amount < limit ? balance - limit : amount) &*&
            balance - result >= limit;
    @*/
{
    //@ open account(myAccount, limit, balance);
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    //@ close account(myAccount, limit, balance - result);
    return result;
}

/***
 * Description:
 * The account_dispose function releases the memory allocated for the given account.
 * @param myAccount - pointer to an existing account to be deleted.
 * The function frees the memory associated with the account,
 * allowing it to be deallocated.
 */
void account_dispose(struct account *myAccount)
    //@ requires account(myAccount, _, _);
    //@ ensures true;
{
    //@ open account(myAccount, _, _);
    free(myAccount);
}

/***
 * Description:
 * The main function first creates an account with a negative limit, 
 * then does some deposits and withdraws and validates the balance is correct,
 * and finally disposes of the account.
 */
int main()
    //@ requires true;
    //@ ensures true;
{
    struct account *myAccount = create_account(-100);
    //@ assert account(myAccount, -100, 0);

    account_deposit(myAccount, 200);
    //@ assert account(myAccount, -100, 200);

    int w1 = account_withdraw(myAccount, 50);
    //@ assert account(myAccount, -100, 150);
    //@ assert w1 == 50;
    assert(w1 == 50);

    int b1 = account_get_balance(myAccount);
    //@ assert b1 == 150;
    assert(b1 == 150);

    int w2 = account_withdraw(myAccount, 300);
    //@ assert w2 == 250;
    //@ assert account(myAccount, -100, -100);
    assert(w2 == 250);

    int b2 = account_get_balance(myAccount);
    //@ assert b2 == -100;
    assert(b2 == -100);

    account_dispose(myAccount);

    return 0;
}
