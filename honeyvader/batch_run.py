#!/usr/bin/python
# -*- coding: utf-8 -*-

import subprocess
import shlex
import os
import Queue
import threading
import csv
# from web3 import Web3

exitFlag = 0
BYTECODE = True
CONTRACT_FOLDER = "temp/"

class honeyvaderThread(threading.Thread):
   def __init__(self, threadID, queue):
      threading.Thread.__init__(self)
      self.threadID = threadID
      self.queue = queue
   def run(self):
      runHoneyVader(self.queue)

def runHoneyVader(queue):
    while not exitFlag:
        queueLock.acquire()
        if not queue.empty():
            contract = queue.get()
            queueLock.release()
            print('Running HoneyVader on contract: '+str(contract).split('/')[-1])
            if BYTECODE:
                cmd = 'python honeyvader.py -si '+str(contract)+' -b -j'
            else:
                cmd = 'python honeyvader.py -si '+str(contract)+' -j'

            # subprocess.call(shlex.split(cmd), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            subprocess.call(shlex.split(cmd))
            print('Running contract '+str(contract).split('/')[-1])+' finished.'
        else:
            queueLock.release()

if __name__ == "__main__":

    queueLock = threading.Lock()
    queue = Queue.Queue()
    # Create new threads
    threads = []
    threadID = 1
    #for i in range(multiprocessing.cpu_count()):
    for i in range(1):
        thread = honeyvaderThread(threadID, queue)
        thread.start()
        threads.append(thread)
        threadID += 1

    # Fill the queue with contracts
    queueLock.acquire()

    # analyzed_contracts = {result_file.split('.')[0] for result_file in os.listdir(os.path.join("..", "results"))}

    f = open("ran.log", "r") # List of log lines
    analyzed_contracts = f.read().split()
    f.close()

    for file in os.listdir(os.path.join("..", "sample_contracts")):
        # if (os.path.join(os.path.join("..", "sample_contracts"), file)) in analyzed_contracts:
        #     print("found")
        #     continue
        if BYTECODE and file.endswith(".bin") or not BYTECODE and file.endswith(".sol"):
            queue.put(os.path.join(os.path.join("..", "sample_contracts"), file))
    queueLock.release()

    print('Verifying: '+str(queue.qsize())+'\n')

    try:
    # Wait for queue to empty
        while not queue.empty():
            pass

        # Notify threads it's time to exit
        exitFlag = 1

        # Wait for all threads to complete
        for t in threads:
            t.join()

        print('\nDone')
    except KeyboardInterrupt:
        exitFlag = 1
        raise
