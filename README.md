# C.R.E.A.M. Collateral Swap

## Note

- this is work in progress
- UI process walkthrough:
    1. user clicks some ui to swap collateral 100 A tokens to collateral B tokens
    2. front end calls flashloanLender to borrow 100 A tokens
    3. crAToken calls this contract's function onFlashLoan, and send 100 A tokens to this contract
    4. swap (100-flashloanFee) A tokens for B tokens
    5. deposit B tokens and get crBTokens
    6. send crBTokens to the user
    7. grab crATokens from the user
    8. withdraw from crATokens and get 100 A tokens
    9. by now the contract has (100 + flashloanFee) A tokens, ready to be grabbed by crAToken for flashloan repayment

    