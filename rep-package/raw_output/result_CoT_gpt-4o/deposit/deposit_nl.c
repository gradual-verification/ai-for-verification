#include "stdlib.h"

/*@
predicate account(struct account* acc; int balance) =
    acc->balance |-> balance;

predicate malloc_block_account(struct account *acc) =
    malloc_block(acc, sizeof(struct account));
@*/

struct account {
    int balance;
};

/*@
requires true;
ensures account(result, 0) &*& malloc_block_account(result);
@*/
struct account *create_account() {
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0) {
        abort();
    }
    myAccount->balance = 0;
    //@ close account(myAccount, 0);
    //@ close malloc_block_account(myAccount);
    return myAccount;
}

/*@
requires account(myAccount, ?balance) &*& myAccount != 0 &*& INT_MIN <= amount &*& amount <= INT_MAX &*& INT_MIN - amount <= balance &*& balance + amount <= INT_MAX;
ensures account(myAccount, balance + amount);
@*/
void account_deposit(struct account *myAccount, int amount) {
    myAccount->balance += amount;
    //@ close account(myAccount, myAccount->balance);
}

/*@
requires account(myAccount, ?balance) &*& myAccount != 0;
ensures account(myAccount, balance) &*& result == balance;
@*/
int account_get_balance(struct account *myAccount) {
    int result = myAccount->balance;
    //@ close account(myAccount, myAccount->balance);
    return result;
}

/*@
requires account(myAccount, ?_) &*& myAccount != 0 &*& INT_MIN <= newBalance &*& newBalance <= INT_MAX;
ensures account(myAccount, newBalance);
@*/
void account_set_balance(struct account *myAccount, int newBalance) {
    myAccount->balance = newBalance;
    //@ close account(myAccount, myAccount->balance);
}

/*@
requires account(myAccount, _) &*& malloc_block_account(myAccount) &*& myAccount != 0;
ensures true;
@*/
void account_dispose(struct account *myAccount) {
    //@ open account(myAccount, _);
    //@ open malloc_block_account(myAccount);
    free(myAccount);
}

int main() 
/*@
requires true;
ensures true;
@*/
{
    struct account *myAccount = create_account();
    account_set_balance(myAccount, 5);
    account_deposit(myAccount, 10);
    int b = account_get_balance(myAccount);
    assert(b == 15);
    account_dispose(myAccount);
    return 0;
}
