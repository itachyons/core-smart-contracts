# iTachyons Contracts

This repository contains all iTachyons Contracts 
that form a core part of the iTachyons PoA blockchain. 

This repository will be updated as and when the blockchain ecosystem grows.

#### Existing Contracts

| Contract Name    | Description                                                                                                                       | Solidity Version(s) |
|------------------|-----------------------------------------------------------------------------------------------------------------------------------|---------------------|
| Migrations       | OnChain migration store for versioning                                                                                            | >=0.4.22 <0.9.0               |
| WBNB             | Wrapped BNB                                                                                                                       | 0.7.6                    |
| Signer           | TTS-20 SIGN token - also redeemable for BEP-20 SIGN                                                                               | >=0.6.0 <0.8.0                    |
| TachyonOracle    | Upgradable Oracle Contract that gives the current price of the Native Asset - TAC                                                 | 0.7.6                    |
| TachyonOracleV2  | V2 of the Oracle Contract that pegs the price of Tac to various blockchain assets                                                 | 0.7.6                    |
| SealerLock       | Contract to onboard new sealers and validators either by Cross Chain BNB Deposit or TAC staking                                   | 0.7.6                    |
| TachyonSale      | Contract to buy/sell TACs cross-chain - Supports only BSC chain at the moment                                                     | 0.7.6                    |
| TachyonXChainBNB | Cross chain contract for the BSC chain to allow swaps between the Tachyon and BSC Chain                                           | >=0.6.0 <0.8.0                    |
| DataFeedFactory  | Factory contract to spawn new DataFeed contracts which would provide an on-chain feed for various pairs like BTC/USD, BNB/USD etc | 0.7.6                    |


