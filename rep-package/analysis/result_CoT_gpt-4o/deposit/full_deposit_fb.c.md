```c
#include "stdlib.h"

struct account
{
    int balance;
};

// Predicate declaration for the account balance
/*@
predicate account_balance(struct account *a, int b) =
    a->balance |-> b;
@*/

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
    return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
//@ requires account_balance(myAccount, ?theBalance) &*& 0 <= amount;
//@ ensures account_balance(myAccount, theBalance + amount);
{
    //@ open account_balance(myAccount, theBalance);
    myAccount->balance += amount;
    //@ close account_balance(myAccount, theBalance + amount);
}

int account_get_balance(struct account *myAccount)
//@ requires account_balance(myAccount, ?balance);
//@ ensures account_balance(myAccount, balance) &*& result == balance;
{
    //@ open account_balance(myAccount, balance);
    int result = myAccount->balance;
    //@ close account_balance(myAccount, balance);
    return result;
}

void account_set_balance(struct account *myAccount, int newBalance)
//@ requires account_balance(myAccount, _);
//@ ensures account_balance(myAccount, newBalance);
{
    //@ open account_balance(myAccount, _);
    myAccount->balance = newBalance;
    //@ close account_balance(myAccount, newBalance);
}

void account_dispose(struct account *myAccount)
//@ requires account_balance(myAccount, _);
//@ ensures true;
{
    //@ open account_balance(myAccount, _);
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
```

### Explanation

- **Predicate Definition**: A predicate `account_balance` is defined to specify the ownership and state of the `balance` field of an `account` struct.
  
- **Function Precondition and Postcondition**: 
  - Each function is equipped with a precondition that specifies the necessary state before execution, often involving the account's balance being correctly initialized or modified.
  - Postconditions guarantee the state after execution, e.g., `create_account` ensures the balance starts at 0, while `account_deposit` increases it appropriately.

- **Memory Safety**:
  - Functions like `account_deposit`, `account_get_balance`, and `account_set_balance` use the `open` and `close` statements to manipulate the predicates for the account's balance, ensuring memory safety.

- **Integer Bounds**:
  - The code ensures non-negative amounts for deposits using the condition `0 <= amount` in `account_deposit`.

- **Resource Deallocation**:
  - `account_dispose` properly frees the allocated memory for an account, ensuring no memory leaks.
  
Using these specifications, VeriFast can verify the correctness and safety of this code in terms of memory use and logical behavior.
