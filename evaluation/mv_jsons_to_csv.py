import json
import csv
from requests import head
import os
import requests

from ethereum_data_etherscan import EthereumData

FOLDER = "money_flow_to_owner_3"

data_file = open('money_flow_to_owner_3.csv', 'w', newline='')
csv_writer = csv.writer(data_file)

def is_token(contract_address):
    # https://ethereum.logic.at/api/v1/account?a=0x42dB5Bfe8828f12F164586AF8A992B3a7B038164
    url = 'https://ethereum.logic.at/api/v1/account?a=' + contract_address
    request_status = requests.get(url)
    print("--------------------------------------------")
    if request_status.status_code != 200:
        print("api error", request_status.status_code)
    else:
        contracts_info = request_status.json()
        contract_info = contracts_info[0]
        tags = contract_info["tags"]
        token_tags = ["ercToken", "nonCompliantToken", "erc1155", "erc1462", "erc1644", "erc20", "erc721", "GasToken"]
        if tags:
            if any(tag in tags for tag in token_tags):
                print("token found", contract_address)
                return True
    print(tags)
    print("not found as token", contract_address, url)
    return False

def has_source_code(contract_address):
    url = 'https://ethereum.logic.at/api/v1/account?a=' + contract_address
    request_status = requests.get(url)
    print("--------------------------------------------")
    if request_status.status_code != 200:
        print("api error", request_status.status_code)
    else:
        contracts_info = request_status.json()
        contract_info = contracts_info[0]
        if not contract_info["source"]:
            return False
    return True

def main():
    count = 0
    api_etherscan = EthereumData()
    # Writing data of CSV file
    for file in os.listdir(os.path.join("Ethereum",FOLDER)):
        row = []
        global contract_data
        print(file)
        if file.endswith(".bin"):
            continue
        contract_data = json.load(open(os.path.join(os.path.join("Ethereum",FOLDER), file)))
        if count == 0:
            header = list(contract_data.keys())
            header = [e for e in header if not e in ("dead_code", "attack_methods", "cashout_methods")]
            header.append("address")
            # detected_by_honeybadger = a honeypot that can be detected before deployment and doing any transaction
            # if a contract has money flow to the owner, but not vulnerable ==> A NEW HONEYPOT!
            header.append("detected_by_honeybadger")
            # header.append("token")
            # header.append("source_code")
            csv_writer.writerow(header)
            count += 1
        contract_data["address"] = file.split('.')[0]
        contract_data["detected_by_honeybadger"] = False
        # contract_data["token"] = False
        # contract_data["source_code"] = False
        # if has_source_code(contract_data.get("address")):
        #     contract_data["source_code"] = True
        if (contract_data.get("inheritance_disorder") or contract_data.get('uninitialised_struct') or contract_data.get("map_key_encoding") or contract_data.get("hidden_transfer") or contract_data.get("balance_disorder") or contract_data.get("skip_empty_string_literal") or contract_data.get("type_deduction_flow")) == True:
            contract_data["detected_by_honeybadger"] = True

        # Find out if the contract is a token or not
        # if contract_data.get("detected_by_honeybadger") == False and contract_data.get("money_flow_to_owner") == True:
        #     if api_etherscan.contract_has_source_code(contract_data.get("address")):
        #         contract_data["source_code"] = True
            # if is_token(contract_data.get("address")):
            #     contract_data["token"] = True
        # if not contract_data.get("errors"):
        #     contract_data["errors"] = "None"
        # else:
        #     contract_data["errors"] = "error"

        for key in header:
            row.append(contract_data.get(key))
        if len(header) != len(row):
            print("Errorrr! " + contract_data["address"])
        if '' in row:
            print("Errorrr! empty row for address "+ contract_data["address"])
        csv_writer.writerow(row)

    data_file.close()

if __name__ == '__main__':
    main()