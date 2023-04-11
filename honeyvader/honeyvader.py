
import opcode
import shlex
import subprocess
import os
import re
import argparse
import logging
import requests
from ethereum_data_etherscan import EthereumData
import symExec
import global_params
import z3
import z3.z3util
import os, glob
import requests
from source_map import SourceMap
from utils import run_command
# from HTMLParser import HTMLParser
import six
import csv


global etherscan_api
etherscan_api = EthereumData()

# TODO Add checks for solc 0.4.25 and z3 4.7.1

def cmd_exists(cmd):
    return subprocess.call(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE) == 0


def cmd_stdout(cmd):
    p = subprocess.Popen(
        cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, err = p.communicate()
    if err:
        return False, output.decode("utf-8")
    else:
        return True, output.decode("utf-8")


def has_dependencies_installed():
    try:
        z3.get_version_string()
    except:
        logging.critical(
            "Z3 is not available. Please install z3 from https://github.com/Z3Prover/z3.")
        return False

    if not cmd_exists("evm"):
        logging.critical(
            "Please install evm from go-ethereum and make sure it is in the path.")
        return False
    # if not evm_cmp_version():
    #     logging.critical("evm version is incompatible.")
    #     return False

    if not cmd_exists("solc --version"):
        logging.critical(
            "solc is missing. Please install the solidity compiler and make sure solc is in the path.")
        return False
    return True


def evm_cmp_version():
    # max_version and min_version need to have the same number of dot separated numbers.
    # The parts of the version need to be convertible to integers.
    max_version_str = "1.8.16"
    min_version_str = "0.0.0"
    max_version = [int(x) for x in max_version_str.split(".")]
    min_version = [int(x) for x in min_version_str.split(".")]

    success, output = cmd_stdout("evm --version")
    if not success or not output:
        logging.critical("Error while determining the version of the evm.")

    version_str = output.split()[2].split("-")[0]
    version = [int(x) for x in version_str.split(".")]

    if len(version) != len(max_version):
        logging.critical("Cannot compare versions: {} (max) and {} (installed).".format(
            max_version_str, version_str))

    for i in range(0, len(max_version)):
        if max_version[i] < version[i]:
            logging.critical("The installed evm version ({}) is too new. HoneyVader supports at most version {}.".format(
                version_str, max_version_str))
            return False
        if min_version[i] > version[i]:
            logging.critical("The installed evm version ({}) is too old. HoneyVader requires at least version {}.".format(
                version_str, min_version_str))
            return False

    return True

def removeSwarmHash(evm):
    evm_without_hash = re.sub(r"a165627a7a72305820\S{64}0029$", "", evm)
    return evm_without_hash


def extract_bin_str(s):
    binary_regex = r"\r?\n======= (.*?) =======\r?\nBinary of the runtime part: \r?\n(.*?)\r?\n"
    contracts = re.findall(binary_regex, s)
    contracts = [contract for contract in contracts if contract[1]]
    if not contracts:
        logging.critical("Solidity compilation failed")
        six.print_({"error": "Solidity compilation failed"})
        exit()
    return contracts


def extract_bin_str_full(s):
    binary_regex = r"\r?\n======= (.*?) =======\r?\nBinary\: \r?\n(.*?)\r?\n"
    contracts = re.findall(binary_regex, s)
    contracts = [contract for contract in contracts if contract[1]]
    if not contracts:
        logging.critical("Solidity compilation failed")
        six.print_({"error": "Solidity compilation failed"})
        exit()
    return contracts


# def _without_metadata(bytecode):
#     print("byte code", bytecode)
#     end = None
#     if (
#         bytecode[-43:-34] == b"\xa1\x65\x62\x7a\x7a\x72\x30\x58\x20"
#         and bytecode[-2:] == b"\x00\x29"
#     ):
#         end = -9 - 32 - 2  # Size of metadata at the end of most contracts
#     print("without metadata", bytecode[:end])
#     return bytecode[:end]


def compileContracts(contract):
    cmd = "solc --bin-runtime %s" % contract
    out = run_command(cmd)
    libs = re.findall(r"_+(.*?)_+", out)
    libs = set(libs)
    if libs:
        return link_full_libraries(contract, libs, extract_bin_str)
    else:
        return extract_bin_str(out)


def compileContractsFullBytecode(contract):
    cmd = "solc --bin %s" % contract
    out = run_command(cmd)
    libs = re.findall(r"_+(.*?)_+", out.decode('utf-8'))
    libs = set(libs)
    if libs:
        return link_full_libraries(contract, libs, extract_bin_str_full)
    else:
        return extract_bin_str_full(out)


def link_libraries(filename, libs, extract_bin_str_fn):
    option = ""
    for idx, lib in enumerate(libs):
        lib_address = "0x" + hex(idx+1)[2:].zfill(40)
        option += " --libraries %s:%s" % (lib, lib_address)
    FNULL = open(os.devnull, 'w')
    cmd = "solc --bin-runtime %s" % filename
    p1 = subprocess.Popen(shlex.split(
        cmd), stdout=subprocess.PIPE, stderr=FNULL)
    cmd = "solc --link%s" % option
    p2 = subprocess.Popen(shlex.split(cmd), stdin=p1.stdout,
                          stdout=subprocess.PIPE, stderr=FNULL)
    p1.stdout.close()
    out = p2.communicate()[0]
    return extract_bin_str_fn(out)

def link_full_libraries(filename, libs, extract_bin_str_fn):
    option = ""
    for idx, lib in enumerate(libs):
        lib_address = "0x" + hex(idx+1)[2:].zfill(40)
        option += " --libraries %s:%s" % (lib, lib_address)
    FNULL = open(os.devnull, 'w')
    cmd = "solc --bin %s" % filename
    p1 = subprocess.Popen(shlex.split(
        cmd), stdout=subprocess.PIPE, stderr=FNULL)
    cmd = "solc --link%s" % option
    p2 = subprocess.Popen(shlex.split(cmd), stdin=p1.stdout,
                          stdout=subprocess.PIPE, stderr=FNULL)
    p1.stdout.close()
    out = p2.communicate()[0].decode()
    return extract_bin_str_fn(out)


def analyze_constructor(processed_evm_file, disasm_file, source_map=None):
    disasm_out = ""
    # disassembles the code (machine language ===> assembly code)
    try:
        disasm_p = subprocess.Popen(
            ["evm", "disasm", processed_evm_file], stdout=subprocess.PIPE)
        disasm_out = disasm_p.communicate()[0].decode()
    except:
        logging.critical("Disassembly failed.")
        exit()
    with open(disasm_file, 'w') as of:
        of.write(disasm_out)
    if source_map is not None:
        symExec.analyze_constructor_variables(
            disasm_file, args.sourceInit, source_map)
    else:
        symExec.analyze_constructor_variables(disasm_file, args.sourceInit)


# disassembles the code (bytecode ===> assembly code)
# bytecode = processed_evm_file
# assembly = disasm_file
def analyze_runtime(solidity, processed_evm_file, disasm_file, constructor_found, source_map=None):
    disasm_out = ""
    try:
        disasm_p = subprocess.Popen(
            ["evm", "disasm", processed_evm_file], stdout=subprocess.PIPE)
        disasm_out = disasm_p.communicate()[0]
    except:
        logging.critical("Disassembly failed.")
        exit()
    with open(disasm_file, 'w') as of:
        of.write(str(disasm_out))
    if source_map is not None:
        symExec.main(solidity, disasm_file, args.sourceInit, constructor_found, source_map)
    else:
        symExec.main(solidity, disasm_file, args.sourceInit, constructor_found)


def remove_temporary_file(path):
    if os.path.isfile(path):
        try:
            os.unlink(path)
        except:
            pass


def split_bytecode(bin_str):

    """
    Compiler version 0.4.*
    CODECOPY: 39
    PUSH1 0X00: 6000
    RETURN: f3
    STOP: 00
    ------------------------------------------
    Compiler version 0.5.* - version 0.6.* - version 0.7.* - version 0.8.*
    CODECOPY: 39
    PUSH1 0X00: 6000
    RETURN: f3
    INVALID: fe    
    """

    if "396000f300" in bin_str:
        # print("compiler version 0.4.*")
        solidity = "= 4"
        split_bytecode = re.split(r'(\s*396000f300\s*)', bin_str)
        constructor_bytecode = split_bytecode[0] + split_bytecode[1]
        runtime_bytecode = split_bytecode[2]
        constructor_found = True
    elif "396000f3fe" in bin_str:
        # print("compiler version >=0.4")
        solidity = ">= 4"
        split_bytecode = re.split(r'(\s*396000f3fe\s*)', bin_str)
        constructor_bytecode = split_bytecode[0] + split_bytecode[1]
        runtime_bytecode = split_bytecode[2]
        constructor_found = True
    else:
        # print("couldn't find the init bytecode")
        solidity = "< 4"
        runtime_bytecode = bin_str
        constructor_bytecode = ""
        constructor_found = False
    return solidity ,constructor_found, constructor_bytecode, runtime_bytecode


def main():
    global args
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("-si", "--sourceInit", type=str,
                       help="local source file name. Solidity by default. Use -b to process evm instead. Use stdin to read from stdin.")
    group.add_argument("-tx", "--transactionhash", type=str,
                       help="search for the transaction hash in etherscan. Could be solidity file/ evm file.")
    parser.add_argument(
        "-b", "--bytecode", help="read bytecode in source instead of solidity file.", action="store_true")

    parser.add_argument(
        "-j", "--json", help="Redirect results to a json file.", action="store_true")
    parser.add_argument("-t", "--timeout", type=int,
                        help="Timeout for Z3 in ms (default "+str(global_params.TIMEOUT)+" ms).")
    parser.add_argument("-gb", "--globalblockchain",
                        help="Integrate with the global ethereum blockchain", action="store_true")
    parser.add_argument("-dl", "--depthlimit", help="Limit DFS depth (default "+str(global_params.DEPTH_LIMIT)+").",
                        action="store", dest="depth_limit", type=int)
    parser.add_argument("-gl", "--gaslimit", help="Limit Gas (default "+str(global_params.GAS_LIMIT)+").",
                        action="store", dest="gas_limit", type=int)
    parser.add_argument(
        "-st", "--state", help="Get input state from state.json", action="store_true")
    parser.add_argument("-ll", "--looplimit", help="Limit number of loops (default "+str(global_params.LOOP_LIMIT)+").",
                        action="store", dest="loop_limit", type=int)
    parser.add_argument("-glt", "--global-timeout", help="Timeout for symbolic execution in sec (default " +
                        str(global_params.GLOBAL_TIMEOUT)+" sec).", action="store", dest="global_timeout", type=int)
    parser.add_argument(
        "--debug", help="Display debug information.", action="store_true")
    parser.add_argument(
        "-c", "--cfg", help="Create control flow graph and store as .dot file.", action="store_true")

    args = parser.parse_args()

    # Set global arguments for symbolic execution
    global_params.USE_GLOBAL_BLOCKCHAIN = 1 if args.globalblockchain else 0
    global_params.INPUT_STATE = 1 if args.state else 0
    global_params.STORE_RESULT = 1 if args.json else 0
    global_params.DEBUG_MODE = 1 if args.debug else 0
    global_params.CFG = 1 if args.cfg else 0
    global_params.BYTECODE = 1 if args.bytecode else 0

    if args.timeout:
        global_params.TIMEOUT = args.timeout
    if args.depth_limit:
        global_params.DEPTH_LIMIT = args.depth_limit
    if args.gas_limit:
        global_params.GAS_LIMIT = args.gas_limit
    if args.loop_limit:
        global_params.LOOP_LIMIT = args.loop_limit
    if args.global_timeout:
        global_params.GLOBAL_TIMEOUT = args.global_timeout

    logging.basicConfig(level=logging.INFO)

    if not has_dependencies_installed():
        return

    # If we are given bytecode, disassemble first, as we need to operate on EVM ASM.
    if args.bytecode:
        
        processed_evm_file = args.sourceInit + '.evm'
        disasm_file = args.sourceInit + '.evm.disasm'
        with open(args.sourceInit) as f:
            evm = f.read()
        solidity, constructor_found, constructor_bytecode, runtime_bytecode = split_bytecode(evm)

        with open(processed_evm_file, 'w') as of:
            of.write(removeSwarmHash(constructor_bytecode))
        # args.source = ../honeypots/MultiplicatorX3.sol
        print("Analysing constructor...")
        analyze_constructor(processed_evm_file, disasm_file)
        remove_temporary_file(processed_evm_file)
        remove_temporary_file(disasm_file)
        remove_temporary_file(disasm_file + '.log')

        with open(processed_evm_file, 'w') as f:
            f.write(removeSwarmHash(runtime_bytecode))

        # args.source = ../honeypots/MultiplicatorX3.sol
        print("Analysing runtime...")
        analyze_runtime(solidity, processed_evm_file, disasm_file, constructor_found)
        remove_temporary_file(processed_evm_file)
        remove_temporary_file(disasm_file)
        remove_temporary_file(disasm_file + '.log')

    elif args.sourceInit:
        # Compile contracts using solc
        # Generates both creation bytecode and runtime bytecode
        contracts = compileContractsFullBytecode(args.sourceInit)
        for cname, bin_str in contracts:
            solidity, constructor_found, constructor_bytecode, runtime_bytecode = split_bytecode(bin_str)
            logging.info("Contract %s:", cname)
            processed_evm_file = cname + '.evm'
            disasm_file = cname + '.evm.disasm'
            with open(processed_evm_file, 'w') as of:
                of.write(removeSwarmHash(constructor_bytecode))

            # args.source = ../honeypots/MultiplicatorX3.sol
            print("Analysing constructor...")
            analyze_constructor(processed_evm_file, disasm_file)
            remove_temporary_file(processed_evm_file)
            remove_temporary_file(disasm_file)
            remove_temporary_file(disasm_file + '.log')

            with open(processed_evm_file, 'w') as of:
                of.write(removeSwarmHash(runtime_bytecode))

            # args.source = ../honeypots/MultiplicatorX3.sol
            print("Analysing runtime...")
            analyze_runtime(solidity,processed_evm_file, disasm_file, constructor_found, SourceMap(cname, args.sourceInit))
            remove_temporary_file(processed_evm_file)
            remove_temporary_file(disasm_file)
            remove_temporary_file(disasm_file + '.log')

        if global_params.STORE_RESULT:
            if ':' in cname:
                # first_part = os.path.join("..", global_params.RESULTS_DIR)
                result_file = os.path.join(global_params.RESULTS_DIR, cname.split(':')[
                                        0].replace('.sol', '.json').split('/')[-1])
                with open(result_file, 'a') as of:
                    of.write("}")

    elif args.transactionhash:
        bytecode = etherscan_api.find_bytecode_from_transaction_hash(args.transactionhash)
        args.source = 'unknown'
        cname = args.transactionhash
        solidity, constructor_found, constructor_bytecode, runtime_bytecode = split_bytecode(bytecode[2:])
        processed_evm_file = args.transactionhash + '.evm'
        disasm_file = args.transactionhash + '.evm.disasm'
        with open(processed_evm_file, 'w') as f:
            f.write(removeSwarmHash(constructor_bytecode))

        print("Analysing constructor...")
        analyze_constructor(processed_evm_file, disasm_file)
        remove_temporary_file(processed_evm_file)
        remove_temporary_file(disasm_file)
        remove_temporary_file(disasm_file + '.log')


        with open(processed_evm_file, 'w') as f:
            f.write(removeSwarmHash(runtime_bytecode))

        print("Analysing runtime...")
        analyze_runtime(solidity, processed_evm_file, disasm_file, constructor_found)

        remove_temporary_file(disasm_file)
        remove_temporary_file(processed_evm_file)
        remove_temporary_file(disasm_file + '.log')
        if global_params.STORE_RESULT:
            if ':' in cname:
                result_file = os.path.join(global_params.RESULTS_DIR, cname.split(':')[
                                        0].replace('.sol', '.json').split('/')[-1])
                with open(result_file, 'a') as of:
                    of.write("}")


if __name__ == '__main__':
    main()