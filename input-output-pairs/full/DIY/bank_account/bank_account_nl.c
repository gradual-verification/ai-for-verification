#include "stdlib.h"

struct bank_account
{
    int balance;
    int account_number;
};

/***
 * Description:
 * The `create_bank_account` function creates a new account with the given account_number. 
 *
 * @param account_number: the given account_number
 *
 * The function makes sure that the created bank_account has its balance as 0 and account number as account_number.
 */
struct bank_account *create_bank_account(int account_number)
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

/***
 * Description:
 * The `bank_account_set_balance` function sets the new balance for the given account.
 *
 * @param myAccount: the given account
 * @param newBalance: the new balanced to be set as
 * 
 * It makes sure that the account has its balance set as newBalance and account number unchanged.
 */
void bank_account_set_balance(struct bank_account *myAccount, int newBalance)
{
    myAccount->balance = newBalance;
}

/***
 * Description:
 * The `bank_account_dispose` function disposes a given account. 
 *
 * @param myAccount: the given account
 * 
 * It makes sure that the bank account is freed. 
 */
void bank_account_dispose(struct bank_account *myAccount)
{
    free(myAccount);

}

/***
 * Description:
 * The `main` function tests the operations of bank_account. 
 */
int main()
{
    struct bank_account *myAccount = create_bank_account(12345);
    bank_account_set_balance(myAccount, 100);
    bank_account_dispose(myAccount);
    return 0;
}
