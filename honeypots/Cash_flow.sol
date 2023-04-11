pragma solidity ^0.4.19;

contract A {
    uint256 public x;
    function test() public{
        x = 3;
    }
}


contract Cash_flow
{
    address owner1 = msg.sender;
    address owner2 = msg.sender;
    address owner3 = msg.sender;
    address owner4 = msg.sender;
    
    function withdraw()
    payable
    public
    {
        require(msg.sender == owner3);
        owner1 = msg.sender;
        // msg.sender.transfer(this.balance);
    }
    
    function test() public{
        require(msg.sender == owner1);
        owner2 = msg.sender;
        owner2.transfer(this.balance);
    }

    function change() public{
        owner3 = msg.sender;
        owner4 = msg.sender;
    }
    
    function play()
    payable
    public
    {
        require(msg.value > 1 ether);
        require(msg.sender == 0x7a617c2B05d2A74Ff9bABC9d81E5225C1e01004b);
        // owner = msg.sender;
    }

    function callA(address _t) public{
        A a = A(_t);
        a.test();
    }
}