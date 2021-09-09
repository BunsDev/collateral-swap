import "@nomiclabs/hardhat-waffle";
import 'hardhat-deploy';
export default {
  defaultNetwork: "hardhat",
  solidity: {
    version: "0.8.2" ,
    settings: {
      optimizer: {
        enabled: true,
        runs: 200
      }
    }
  },
  networks: {
    hardhat: {
      forking: {
        url: "https://mainnet-eth.compound.finance/",
        blockNumber: 13099508

      }
    }
  },
  mocha: {
    timeout: 600000
  }
};
