#include "stdlib.h"

struct bank_account
{
    int balance;
    int account_number;
};

/*@ 
predicate bank_acc_balance(struct bank_account *acc, int balance) = acc->balance |-> balance;
predicate bank_acc_number(struct bank_account *acc, int account_number) = acc->account_number |-> account_number;
@*/

struct bank_account *create_bank_account(int account_number)
//@ requires true;
//@ ensures bank_acc_balance(result, 0) &*& bank_acc_number(result, account_number);
{
    struct bank_account *myAccount = malloc(sizeof(struct bank_account));
    if (myAccount == 0)
    {
        abort();
    }
    myAccount->balance = 0;
    myAccount->account_number = account_number;
    
    return myAccount;
}

void bank_account_set_balance(struct bank_account *myAccount, int newBalance)
//@ requires bank_acc_balance(myAccount, _) &*& bank_acc_number(myAccount, _);
//@ ensures bank_acc_balance(myAccount, newBalance) &*& bank_acc_number(myAccount, _);
{
    myAccount->balance = newBalance;
}

void bank_account_dispose(struct bank_account *myAccount)
//@ requires bank_acc_balance(myAccount, _) &*& bank_acc_number(myAccount, _);
//@ ensures true;
{
    free(myAccount);

}

int main()
//@ requires true;
//@ ensures true;
{
    struct bank_account *myAccount = create_bank_account(12345);
    bank_account_set_balance(myAccount, 100);
    bank_account_dispose(myAccount);
    return 0;
}
