# this the interface to create your own data source 
# this class pings etherscan to get the latest code and balance information

import json
import re
import requests

class EthereumData:
	def __init__(self):
		self.apiDomain = "https://api.etherscan.io/api"
		self.apiDomain_bsc = "https://api.bscscan.com/api"
		self.apikey = "VT4IW6VK7VES1Q9NYFI74YKH8U7QW9XRHN"
		self.apikey_bsc = 'WKR2TT211YBPU6NN1G8419R964C23F7HEK'

	def getBalance(self, address):
		apiEndPoint = self.apiDomain + "?module=account&action=balance&address=" + address + "&tag=latest&apikey=" + self.apikey
		r = requests.get(apiEndPoint)
		result = json.loads(r.text)
		status = result['message']
		if status == "OK":
			return result['result'] 
		return -1

	def getCode(self, address):
		# apiEndPoint = self.apiDomain + "" + address + "&tag=latest&apikey=" + apikey
		# no direct endpoint for this
		r = requests.get("https://etherscan.io/address/" + address + "#code")
		html = r.text
		code = re.findall("<div id='verifiedbytecode2'>(\w*)<\/div>", html)[0]
		return code

	def find_bytecode_from_transaction_hash(self, tx_hash):
		# https://api.etherscan.io/api?module=proxy&action=eth_getTransactionByHash&txhash=0x00380be2db85b058cb8c5c9061ab46a9c563e87c36a48782859c2fc7e9886e8c&apikey=YourApiKeyToken
		# https://api.bscscan.com/api?module=proxy&action=eth_getTransactionByHash&txhash=0x2836de456b2e24a1efc394774737e66ce44f9f0473dfbaa7370eda6fad686ed2&apikey=YourApiKeyToken
		url = self.apiDomain + '?module=proxy&action=eth_getTransactionByHash&txhash=' + tx_hash + '&apikey=' + self.apikey
		request_status = requests.get(url)
		if request_status.status_code == 200:
			txinfo = request_status.json()
		tx_result = txinfo["result"]
		init_bytecode = tx_result['input']
		return init_bytecode