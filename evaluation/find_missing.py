import csv
import json

hashes1 = set()
hashes2 = set()
with open("./ethereum_dataset.csv", 'r') as f:
    next(f)
    for line in f:
        if not line:
            continue

        th = line.split(',')[1].strip()
        if th in hashes1:
            print("1 FOUND DUPLICATE ", th)

        hashes1.add(th)

with open(r"C:\Users\AR01530\Desktop\Tools\test2\HoneyBadger\etherscan_dataset.log", 'r') as f:
    for line in f:
        i = line.find("'transactionHash':")
        sq1 = line.find("'", i+len("'transactionHash':"))
        sq2 = line.find("'", sq1 + 1)
        th = line[sq1+1:sq2]
        if th in hashes2:
            print("2 FOUND DUPLICATE ", th)
            
        hashes2.add(th)

# print(hashes1.symmetric_difference(hashes2))
# print(hashes1.intersection(hashes2))

print("Hashes missing from ethereum_dataset.csv = %s" % hashes2.difference(hashes1))
print()
print("Hashes missing from dataset.log = %s" % hashes1.difference(hashes2))