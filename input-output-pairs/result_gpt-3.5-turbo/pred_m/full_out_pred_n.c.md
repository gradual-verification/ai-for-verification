```c
#include "stdlib.h"

struct account
{
    int limit;
    int balance;
};

/*@
predicate account(struct account *acc, int limit, int balance) =
    acc != NULL &*&
    malloc_block_account(acc) &*&
    acc->limit |-> limit &*&
    acc->balance |-> balance;

lemma void create_account_spec(struct account *acc)
requires acc == NULL;
ensures account(acc, ?l, 0) &*& l <= 0;
{
    open account(acc, _, _);
    close account(acc, l, 0);
}

lemma void account_deposit_spec(struct account *acc, int amount)
requires account(acc, ?l, ?b) &*& amount >= 0;
ensures account(acc, l, b + amount);
{}

lemma void account_withdraw_spec(struct account *acc, int amount)
requires account(acc, ?l, ?b) &*& amount >= 0;
ensures account(acc, l, b - result) &*& result == (b - amount < l ? b - l : amount);
{}

lemma void account_dispose_spec(struct account *acc)
requires account(acc, _, _);
ensures true;
{}

struct account *create_account(int limit)
//@ requires limit <= 0;
//@ ensures account(result, limit, 0);
{
    struct account *myAccount = malloc(sizeof(struct account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->limit = limit;
    myAccount->balance = 0;
    create_account_spec(myAccount);
    return myAccount;
}

int account_get_balance(struct account *myAccount)
//@ requires account(myAccount, ?l, ?b);
//@ ensures account(myAccount, l, b) &*& result == b;
{
    int result = myAccount->balance;
    return result;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account(myAccount, ?l, ?b) &*& amount >= 0;
//@ ensures account(myAccount, l, b + amount);
{
    myAccount->balance += amount;
    account_deposit_spec(myAccount, amount);
}

int account_withdraw(struct account *myAccount, int amount)
//@ requires account(myAccount, ?l, ?b) &*& amount >= 0;
//@ ensures account(myAccount, l, b - result) &*& result == (b - amount < l ? b - l : amount);
{
    int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
    myAccount->balance -= result;
    account_withdraw_spec(myAccount, amount);
    return result;
}

void account_dispose(struct account *myAccount)
//@ requires account(myAccount, _, _);
//@ ensures true;
{
    account_dispose_spec(myAccount);
    free(myAccount);
}

int main()
//@ ensures true;
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
```

