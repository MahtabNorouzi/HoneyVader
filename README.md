To run HoneyVader, plesae download the project and use the created docker image for Honeybadger using the following command:
  docker run -it --rm -v (the path of the project folder):/root christoftorres/honeybadger
  
To test HoneyVader, please use the following commands:
  pip install --upgrade pip
  pip install unidecode
  
  (using source code)
  python honeyvader.py -si ../honeypots/For_Test.sol
  
  (using bytecode)
  python honeyvader.py -si ../honeypots/X2_FLASH.bin -b
