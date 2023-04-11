import pprint
import collections
import tokenize
# import sha3
from tokenize import NUMBER, NAME, NEWLINE
import re
import math
import sys
import pickle
import json
import traceback
import signal
import time
import logging
import os.path
import z3
import binascii
import global_params
import six
import os
import errno
import pdb
# import numpy as np

from collections import namedtuple
from vargenerator import *
from ethereum_data_etherscan import *
from basicblock import BasicBlock
from analysis import *
from decimal import Decimal
# from unidecode import unidecode

pretty_printer = pprint.PrettyPrinter()

# logging.basicConfig(filename="newfile.log",level=logging.INFO,filemode='w')
log = logging.getLogger(__name__)
UNSIGNED_BOUND_NUMBER = 2**256 - 1
CONSTANT_ONES_159 = BitVecVal((1 << 160) - 1, 256)


def enum(**named_values):
    return type('Enum', (), named_values)


HeuristicTypes = enum(
    MONEY_FLOW="Money flow",
    MONEY_FLOW_TO_OWNER="Money flow to owner",
    FAKE_CALL_TRICK="Fake call trick",
    FAKE_OWNERCHANGE_TRICK="Fake ownerchange trick",
    MAP_KEY_ENCODING="Map key encoding",
    RACING_TIME="Racing time"
)


class Parameter:
    def __init__(self, **kwargs):
        attr_defaults = {
            "instr": "",
            "block": 0,
            "depth": 0,
            "pre_block": 0,
            "func_call": -1,
            "stack": [],
            "calls": [],
            "memory": [],
            "models": [],
            "visited": [],
            "visited_edges": {},
            "mem": {},
            "analysis": {},
            "sha3_list": {},
            "global_state": {},
            "is_feasible": True,
            "path_conditions_and_vars": {}
        }
        for (attr, default) in six.iteritems(attr_defaults):
            setattr(self, attr, kwargs.get(attr, default))

    def copy(self):
        _kwargs = custom_deepcopy(self.__dict__)
        return Parameter(**_kwargs)


def initGlobalVars():
    global solver
    # Z3 solver
    solver = Solver()
    solver.set("timeout", global_params.TIMEOUT)

    global visited_pcs
    visited_pcs = set()

    global results
    results = {
        "evm_code_coverage": "", "execution_time": "", "dead_code": [], "errors": "None",
        "execution_paths": "", "timeout": False, "money_flow": False,
        "money_flow_to_owner": False,
        "map_key_encoding": False,
        "racing_time": False,
        "fake_call_trick": False, "fake_ownerchange_trick": False,
        "constructor_found": False, "owner_aware": False, 
        "solidity_version": "",
        "attack_methods": [], "cashout_methods": []
    }

    global g_timeout
    g_timeout = False

    global h_timeout
    h_timeout = False

    global feasible_blocks
    feasible_blocks = []

    global infeasible_blocks
    infeasible_blocks = []

    global execution_paths
    execution_paths = {}

    global list_of_comparisons
    list_of_comparisons = {}

    global list_of_functions
    list_of_functions = {}

    global list_of_structs
    list_of_structs = []

    global list_of_sstores
    list_of_sstores = []

    global list_of_calls
    list_of_calls = {}

    global list_of_hashes
    list_of_hashes = []

    global list_of_suicides
    list_of_suicides = []

    global list_of_vars
    list_of_vars = {}

    global list_of_multiplications
    list_of_multiplications = {}

    global list_of_additions
    list_of_additions = {}

    global terminals
    terminals = []

    global message_value
    message_value = None

    global message_sender
    message_sender = None

    global tx_origin
    tx_origin = None

    global timestamp
    timestamp = None

    global account_balance
    account_balance = None

    global suicidal
    suicidal = False

    global heuristics
    heuristics = []

    # capturing the last statement of each basic block
    global end_ins_dict
    end_ins_dict = {}

    # capturing all the instructions, keys are corresponding addresses
    global instructions
    instructions = {}

    # capturing the "jump type" of each basic block
    global jump_type
    jump_type = {}

    global vertices
    vertices = {}

    global edges
    edges = {}

    # store the path condition corresponding to each path in money_flow_all_paths
    global path_conditions
    path_conditions = []

    # store global variables, e.g. storage, balance of all paths
    global all_gs
    all_gs = []

    global total_no_of_paths
    total_no_of_paths = 0

    global no_of_test_cases
    no_of_test_cases = 0

    # to generate names for symbolic variables
    global gen
    gen = Generator()

    global data_source
    if global_params.USE_GLOBAL_BLOCKCHAIN:
        data_source = EthereumData()

    global log_file
    log_file = open(c_name + '.log', "w")


def change_format():
    with open(c_name) as disasm_file:
        file_contents = disasm_file.readlines()
        i = 0
        firstLine = file_contents[0].strip('\n')
        for line in file_contents:
            line = line.replace('SELFDESTRUCT', 'SUICIDE')
            line = line.replace('Missing opcode 0xfd', 'REVERT')
            line = line.replace('Missing opcode 0xfe', 'ASSERTFAIL')
            line = line.replace('Missing opcode', 'INVALID')
            line = line.replace(':', '')
            lineParts = line.split(' ')
            try:  # removing initial zeroes
                lineParts[0] = str(int(lineParts[0]))

            except:
                lineParts[0] = lineParts[0]
            lineParts[-1] = lineParts[-1].strip('\n')
            try:  # adding arrow if last is a number
                lastInt = lineParts[-1]
                if(int(lastInt, 16) or int(lastInt, 16) == 0) and len(lineParts) > 2:
                    lineParts[-1] = "=>"
                    lineParts.append(lastInt)
            except Exception:
                pass
            file_contents[i] = ' '.join(lineParts)
            i = i + 1
        file_contents[0] = firstLine
        file_contents[-1] += '\n'

    with open(c_name, 'w') as disasm_file:
        disasm_file.write("\n".join(file_contents))


def build_cfg_and_analyze():
    global source_map

    change_format()
    with open(c_name, 'r') as disasm_file:
        disasm_file.readline()  # Remove first line
        tokens = tokenize.generate_tokens(disasm_file.readline)
        collect_vertices(tokens)
        construct_bb()
        construct_static_edges()
        full_sym_exec()  # jump targets are constructed on the fly
        if global_params.CFG:
            print_cfg()


def print_cfg():
    f = open(c_name.replace('.disasm', '').replace(':', '-')+'.dot', 'w')
    f.write('digraph honeyvader_cfg {\n')
    f.write('rankdir = TB;\n')
    f.write('size = "240"\n')
    f.write(
        'graph[fontname = Courier, fontsize = 14.0, labeljust = l, nojustify = true];node[shape = record];\n')
    address_width = 10
    if len(hex(instructions.keys()[-1])) > address_width:
        address_width = len(hex(instructions.keys()[-1]))
    for block in vertices.values():
        # block.display()
        address = block.get_start_address()
        label = '"'+hex(block.get_start_address())+'"[label="'
        for instruction in block.get_instructions():
            label += "{0:#0{1}x}".format(address,
                                         address_width)+" "+instruction+"\l"
            address += 1 + (len(instruction.split(' ')
                            [1].replace("0x", "")) / 2)
        if block.get_start_address() in infeasible_blocks:
            f.write(label+'",style=filled,color=gray];\n')
        else:
            f.write(label+'"];\n')
        if block.get_block_type() == "conditional":
            if len(edges[block.get_start_address()]) > 1:
                true_branch = block.get_branch_expression()
                if is_expr(true_branch):
                    true_branch = simplify(true_branch)
                f.write('"'+hex(block.get_start_address())+'" -> "'+hex(
                    edges[block.get_start_address()][1])+'" [color="green" label=" '+str(true_branch)+'"];\n')
                false_branch = Not(block.get_branch_expression())
                if is_expr(false_branch):
                    false_branch = simplify(false_branch)
                f.write('"'+hex(block.get_start_address())+'" -> "'+hex(
                    edges[block.get_start_address()][0])+'" [color="red" label=" '+str(false_branch)+'"];\n')
            else:
                f.write('"'+hex(block.get_start_address()) +
                        '" -> "UNKNOWN_TARGET" [color="black" label=" UNKNOWN_BRANCH_EXPR"];\n')
                f.write('"'+hex(block.get_start_address())+'" -> "' +
                        hex(edges[block.get_start_address()][0])+'" [color="black"];\n')
        elif block.get_block_type() == "unconditional" or block.get_block_type() == "falls_to":
            if len(edges[block.get_start_address()]) > 0:
                for i in range(len(edges[block.get_start_address()])):
                    f.write('"'+hex(block.get_start_address())+'" -> "' +
                            hex(edges[block.get_start_address()][i])+'" [color="black"];\n')
            else:
                f.write('"'+hex(block.get_start_address()) +
                        '" -> "UNKNOWN_TARGET" [color="black"];\n')
    f.write('}\n')
    f.close()
    log.debug(str(edges))


def mapping_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global source_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            if name.startswith("PUSH"):
                if name == "PUSH":
                    value = positions[idx]['value']
                    instr_value = current_line_content.split(" ")[1]
                    if int(value, 16) == int(instr_value, 16):
                        source_map.instr_positions[current_ins_address] = source_map.positions[idx]
                        idx += 1
                        break
                    else:
                        raise Exception("Source map error")
                else:
                    source_map.instr_positions[current_ins_address] = source_map.positions[idx]
                    idx += 1
                    break
            else:
                raise Exception("Source map error")
    return idx


def mapping_non_push_instruction(current_line_content, current_ins_address, idx, positions, length):
    global source_map

    while (idx < length):
        if not positions[idx]:
            return idx + 1
        name = positions[idx]['name']
        if name.startswith("tag"):
            idx += 1
        else:
            instr_name = current_line_content.split(" ")[0]
            if name == instr_name or name == "INVALID" and instr_name == "ASSERTFAIL" or name == "KECCAK256" and instr_name == "SHA3" or name == "SELFDESTRUCT" and instr_name == "SUICIDE":
                source_map.instr_positions[current_ins_address] = source_map.positions[idx]
                idx += 1
                break
            else:
                raise Exception("Source map error")
    return idx

# 1. Parse the disassembled file
# 2. Then identify each basic block (i.e. one-in, one-out)
# 3. Store them in vertices


def collect_vertices(tokens):
    global source_map
    if source_map:
        idx = 0
        positions = source_map.positions
        length = len(positions)
    global end_ins_dict
    global instructions
    global jump_type

    current_ins_address = 0
    last_ins_address = 0
    is_new_line = True
    current_block = 0
    current_line_content = ""
    wait_for_push = False
    is_new_block = False

    for tok_type, tok_string, (srow, scol), _, line_number in tokens:
        if wait_for_push is True:
            push_val = ""
            for ptok_type, ptok_string, _, _, _ in tokens:
                if ptok_type == NEWLINE:
                    is_new_line = True
                    current_line_content += push_val + ' '
                    instructions[current_ins_address] = current_line_content
                    idx = mapping_push_instruction(
                        current_line_content, current_ins_address, idx, positions, length) if source_map else None
                    log.debug(current_line_content)
                    current_line_content = ""
                    wait_for_push = False
                    break
                try:
                    int(ptok_string, 16)
                    push_val += ptok_string
                except ValueError:
                    pass
            continue
        elif is_new_line is True and tok_type == NUMBER:  # looking for a line number
            last_ins_address = current_ins_address
            try:
                current_ins_address = int(tok_string)
            except ValueError:
                log.critical("ERROR when parsing row %d col %d", srow, scol)
                quit()
            is_new_line = False
            if is_new_block:
                current_block = current_ins_address
                is_new_block = False
            continue
        elif tok_type == NEWLINE:
            is_new_line = True
            log.debug(current_line_content)
            instructions[current_ins_address] = current_line_content
            idx = mapping_non_push_instruction(
                current_line_content, current_ins_address, idx, positions, length) if source_map else None
            current_line_content = ""
            continue
        elif tok_type == NAME:
            if tok_string == "JUMPDEST":
                if last_ins_address not in end_ins_dict:
                    end_ins_dict[current_block] = last_ins_address
                current_block = current_ins_address
                is_new_block = False
            elif tok_string == "STOP" or tok_string == "RETURN" or tok_string == "SUICIDE" or tok_string == "REVERT" or tok_string == "ASSERTFAIL":
                jump_type[current_block] = "terminal"
                end_ins_dict[current_block] = current_ins_address
            elif tok_string == "JUMP":
                jump_type[current_block] = "unconditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string == "JUMPI":
                jump_type[current_block] = "conditional"
                end_ins_dict[current_block] = current_ins_address
                is_new_block = True
            elif tok_string.startswith('PUSH', 0):
                wait_for_push = True
            is_new_line = False
        if tok_string != "=" and tok_string != ">":
            current_line_content += tok_string + " "

    if current_block not in end_ins_dict:
        log.debug("current block: %d", current_block)
        log.debug("last line: %d", current_ins_address)
        end_ins_dict[current_block] = current_ins_address

    if current_block not in jump_type:
        jump_type[current_block] = "terminal"

    for key in end_ins_dict:
        if key not in jump_type:
            jump_type[key] = "falls_to"


def construct_bb():
    global vertices
    global edges
    sorted_addresses = sorted(instructions.keys())
    size = len(sorted_addresses)
    for key in end_ins_dict:
        end_address = end_ins_dict[key]
        block = BasicBlock(key, end_address)
        if key not in instructions:
            continue
        block.add_instruction(instructions[key])
        i = sorted_addresses.index(key) + 1
        while i < size and sorted_addresses[i] <= end_address:
            block.add_instruction(instructions[sorted_addresses[i]])
            i += 1
        block.set_block_type(jump_type[key])
        vertices[key] = block
        edges[key] = []


def construct_static_edges():
    add_falls_to()  # these edges are static


def add_falls_to():
    global vertices
    global edges
    key_list = sorted(jump_type.keys())
    length = len(key_list)
    for i, key in enumerate(key_list):
        if jump_type[key] != "terminal" and jump_type[key] != "unconditional" and i+1 < length:
            target = key_list[i+1]
            edges[key].append(target)
            vertices[key].set_falls_to(target)


def get_name_for(var_name):
    global is_constructor
    if is_constructor:
        return "constructor_" + var_name
    else:
        return var_name


def get_init_global_state(path_conditions_and_vars):
    global message_value
    global message_sender
    global tx_origin
    global timestamp

    global_state = {"balance": {}, "pc": 0}
    init_is = init_ia = deposited_value = sender_address = receiver_address = gas_price = origin = currentCoinbase = currentNumber = currentDifficulty = currentGasLimit = tx_origin = timestamp = callData = None

    if global_params.INPUT_STATE:
        with open('state.json') as f:
            state = json.loads(f.read())
            if state["Is"]["balance"]:
                init_is = int(state["Is"]["balance"], 16)
            if state["Ia"]["balance"]:
                init_ia = int(state["Ia"]["balance"], 16)
            if state["exec"]["value"]:
                deposited_value = 0
            if state["Is"]["address"]:
                sender_address = int(state["Is"]["address"], 16)
            if state["Ia"]["address"]:
                receiver_address = int(state["Ia"]["address"], 16)
            if state["exec"]["gasPrice"]:
                gas_price = int(state["exec"]["gasPrice"], 16)
            if state["exec"]["origin"]:
                origin = int(state["exec"]["origin"], 16)
            if state["env"]["currentCoinbase"]:
                currentCoinbase = int(state["env"]["currentCoinbase"], 16)
            if state["env"]["currentNumber"]:
                currentNumber = int(state["env"]["currentNumber"], 16)
            if state["env"]["currentDifficulty"]:
                currentDifficulty = int(state["env"]["currentDifficulty"], 16)
            if state["env"]["currentGasLimit"]:
                currentGasLimit = int(state["env"]["currentGasLimit"], 16)

    # for some weird reason these 3 vars are stored in path_conditions instead of global_state
    else:
        sender_address = BitVec("Is", 256)
        receiver_address = BitVec(get_name_for("Ia"), 256)
        deposited_value = BitVec(get_name_for("Iv"), 256)
        init_is = BitVec(get_name_for("init_Is"), 256)
        init_ia = BitVec(get_name_for("init_Ia"), 256)

    path_conditions_and_vars["Is"] = sender_address
    path_conditions_and_vars["Ia"] = receiver_address
    path_conditions_and_vars["Iv"] = deposited_value

    message_value = deposited_value
    message_sender = sender_address

    constraint = (deposited_value >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = (init_is >= deposited_value)
    path_conditions_and_vars["path_condition"].append(constraint)
    constraint = (init_ia >= BitVecVal(0, 256))
    path_conditions_and_vars["path_condition"].append(constraint)

    # adding new constraints to the solver for US, HT, and RT
    # ** Uninitalized Struct : Is >= 20
    constraint = (UGE(Extract(159, 0, message_sender), 30))
    path_conditions_and_vars["path_condition"].append(constraint)

    # update the balances of the "caller" and "callee"

    global_state["balance"]["Is"] = (init_is - deposited_value)
    global_state["balance"]["Ia"] = (init_ia + deposited_value)

    if not gas_price:
        new_var_name = gen.gen_gas_price_var()
        gas_price = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = gas_price

    if not origin:
        new_var_name = gen.gen_origin_var()
        origin = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = origin
        tx_origin = origin

    if not currentCoinbase:
        new_var_name = get_name_for("IH_c")
        currentCoinbase = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentCoinbase

    if not currentNumber:
        new_var_name = get_name_for("IH_i")
        currentNumber = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentNumber
    # ** Hidden Transfer : block_number > 5040272
        constraint = (UGE(currentNumber, 6000000))
        path_conditions_and_vars["path_condition"].append(constraint)

    if not currentDifficulty:
        new_var_name = get_name_for("IH_d")
        currentDifficulty = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentDifficulty

    if not currentGasLimit:
        new_var_name = get_name_for("IH_l")
        currentGasLimit = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = currentGasLimit

    new_var_name = get_name_for("IH_s")
    currentTimestamp = BitVec(new_var_name, 256)
    path_conditions_and_vars[new_var_name] = currentTimestamp
    timestamp = currentTimestamp


    # the state of the current current contract
    if "Ia" not in global_state:
        global_state["Ia"] = {}
    global_state["miu_i"] = 0
    global_state["value"] = deposited_value
    global_state["sender_address"] = sender_address
    global_state["receiver_address"] = receiver_address
    global_state["gas_price"] = gas_price
    global_state["origin"] = origin
    global_state["currentCoinbase"] = currentCoinbase
    global_state["currentTimestamp"] = currentTimestamp
    global_state["currentNumber"] = currentNumber
    global_state["currentDifficulty"] = currentDifficulty
    global_state["currentGasLimit"] = currentGasLimit

    return global_state


def full_sym_exec():
    # executing, starting from beginning
    path_conditions_and_vars = {"path_condition": []}
    global_state = get_init_global_state(path_conditions_and_vars)
    analysis = init_analysis()
    params = Parameter(path_conditions_and_vars=path_conditions_and_vars,
                       global_state=global_state, analysis=analysis)
    execution_paths[total_no_of_paths] = []
    return sym_exec_block(params)


# Symbolically executing a block from the start address
def sym_exec_block(params):
    global solver
    #global visited_edges
    global path_conditions
    global all_gs
    global results
    global source_map
    global terminals
    global loop_limits

    block = params.block
    pre_block = params.pre_block
    visited = params.visited
    visited_edges = params.visited_edges
    depth = params.depth
    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    analysis = params.analysis
    models = params.models
    calls = params.calls
    func_call = params.func_call

    # Factory Function for tuples is used as dictionary key
    Edge = namedtuple("Edge", ["v1", "v2"])
    if block < 0:
        log.debug("UNKNOWN JUMP ADDRESS. TERMINATING THIS PATH")
        return ["ERROR"]

    if global_params.DEBUG_MODE:
        print("Reach block address " + hex(block))
        #print("STACK: " + str(stack))

    current_edge = Edge(pre_block, block)
    if current_edge in visited_edges:
        updated_count_number = visited_edges[current_edge] + 1
        visited_edges.update({current_edge: updated_count_number})
    else:
        visited_edges.update({current_edge: 1})

    if visited_edges[current_edge] > global_params.LOOP_LIMIT:
        if jump_type[pre_block] == "conditional" and vertices[pre_block].get_falls_to() == block:
            if global_params.DEBUG_MODE:
                print(
                    "!!! Overcome a number of loop limit. Terminating this path ... !!!")
            return stack

    current_gas_used = analysis["gas"]
    if current_gas_used > global_params.GAS_LIMIT:
        if global_params.DEBUG_MODE:
            print("!!! Run out of gas. Terminating this path ... !!!")
        return stack

    # Execute every instruction, one at a time
    try:
        block_ins = vertices[block].get_instructions()
    except KeyError:
        if global_params.DEBUG_MODE:
            print("This path results in an exception, possibly an invalid jump address")
        return ["ERROR"]

    for instr in block_ins:
        if global_params.DEBUG_MODE:
            print(hex(global_state["pc"])+" \t "+str(instr))
        params.instr = instr
        sym_exec_ins(params)
    if global_params.DEBUG_MODE:
        print("")

    try:
        # Search for structs inside basic block
        sequence_of_instructions = ""
        for index in instructions:
            if index >= vertices[block].get_start_address() and index <= vertices[block].get_end_address():
                sequence_of_instructions += str(index)+" "+instructions[index]
        matches = re.compile(
            "[0-9]+ DUP2 [0-9]+ PUSH1 0x([0-9]+) [0-9]+ ADD .+? [0-9]+ SWAP1 ([0-9]+) SSTORE").findall(sequence_of_instructions)
        if matches:
            # Check that that struct has more than one element and that the first element is stored to address 0
            if len(matches) > 1 and int(matches[0][0]) == 0:
                for match in matches:
                    struct = {}
                    struct["path_condition"] = path_conditions_and_vars["path_condition"]
                    struct["function_signature"] = get_function_signature_from_path_condition(
                        struct["path_condition"])
                    struct["address"] = int(match[0])
                    struct["block"] = params.block
                    struct["pc"] = int(match[1])
                    if not struct in list_of_structs:
                        list_of_structs.append(struct)
        else:
            matches = re.compile(
                "[0-9]+ DUP2 ([0-9]+) SSTORE .+? [0-9]+ PUSH1 0x[0-9]+ [0-9]+ DUP[0-9] [0-9]+ ADD [0-9]+ SSTORE").findall(sequence_of_instructions)
            if matches:
                for sstore in list_of_sstores:
                    if sstore["pc"] == int(matches[0]) and sstore["address"] == 0:
                        struct = {}
                        struct["path_condition"] = path_conditions_and_vars["path_condition"]
                        struct["function_signature"] = sstore["function_signature"]
                        struct["address"] = sstore["address"]
                        struct["block"] = params.block
                        struct["pc"] = sstore["pc"]
                        if not struct in list_of_structs:
                            list_of_structs.append(struct)
    except:
        pass

    # Mark that this basic block in the visited blocks
    visited.append(block)
    depth += 1

    # Go to next Basic Block(s)
    if jump_type[block] == "terminal" or depth > global_params.DEPTH_LIMIT:
        global total_no_of_paths

        total_no_of_paths += 1

        terminal = {}
        terminal["opcode"] = block_ins = vertices[block].get_instructions(
        )[-1].replace(" ", "")
        terminal["path_condition"] = path_conditions_and_vars["path_condition"]
        terminals.append(terminal)

        if global_params.DEBUG_MODE:
            if depth > global_params.DEPTH_LIMIT:
                six.print_("!!! DEPTH LIMIT EXCEEDED !!!")

        if global_params.DEBUG_MODE:
            six.print_("Termintating path: "+str(total_no_of_paths))
            six.print_("Depth: "+str(depth))
            six.print_("")

        display_analysis(analysis)

    elif jump_type[block] == "unconditional":  # executing "JUMP"
        successor = vertices[block].get_jump_target()
        new_params = params.copy()
        new_params.depth = depth
        new_params.block = successor
        new_params.pre_block = block
        new_params.visited_edges = visited_edges
        new_params.global_state["pc"] = successor
        if source_map:
            source_code = source_map.find_source_code(global_state["pc"])
            if source_code in source_map.func_call_names:
                new_params.func_call = global_state["pc"]
        sym_exec_block(new_params)
    elif jump_type[block] == "falls_to":  # just follow to the next basic block
        successor = vertices[block].get_falls_to()
        new_params = params.copy()
        new_params.depth = depth
        new_params.block = successor
        new_params.pre_block = block
        new_params.visited_edges = visited_edges
        new_params.global_state["pc"] = successor
        sym_exec_block(new_params)
    elif jump_type[block] == "conditional":  # executing "JUMPI"
        # A choice point, we proceed with depth first search

        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})

        current_execution_path = copy.deepcopy(
            execution_paths[total_no_of_paths])

        branch_expression = vertices[block].get_branch_expression()
        negated_branch_expression = Not(branch_expression)

        solver.reset()
        solver.add(path_conditions_and_vars["path_condition"])

        if global_params.DEBUG_MODE:
            print("Negated branch expression: " +
                  remove_line_break_space(negated_branch_expression))

        if not negated_branch_expression in list_of_comparisons:
            list_of_comparisons[negated_branch_expression] = get_function_signature_from_path_condition(
                path_conditions_and_vars["path_condition"])

        solver.add(negated_branch_expression)

        isRightBranchFeasible = True

        try:
            try:
                if solver.check() == unsat and not (negated_branch_expression == True or negated_branch_expression == False or negated_branch_expression == Not(True) or negated_branch_expression == Not(False)):
                    isRightBranchFeasible = False
            except:
                isRightBranchFeasible = False
            if not isRightBranchFeasible:
                if not vertices[block].get_falls_to() in feasible_blocks:
                    infeasible_blocks.append(vertices[block].get_falls_to())
                if global_params.DEBUG_MODE:
                    print("RIGHT BRANCH IS INFEASIBLE ("+str(solver.check())+")")
            else:
                if vertices[block].get_falls_to() in infeasible_blocks:
                    infeasible_blocks.remove(vertices[block].get_falls_to())
                    for heuristic in heuristics:
                        if heuristic["block"] == vertices[block].get_falls_to():
                            heuristics.remove(heuristic)
                feasible_blocks.append(vertices[block].get_falls_to())
            right_branch = vertices[block].get_falls_to()
            new_params = params.copy()
            new_params.depth = depth
            new_params.block = right_branch
            new_params.pre_block = block
            new_params.visited_edges = visited_edges
            new_params.global_state["pc"] = right_branch
            new_params.is_feasible = isRightBranchFeasible
            new_params.path_conditions_and_vars["path_condition"].append(
                negated_branch_expression)
            sym_exec_block(new_params)
        except Exception as e:
            log_file.write(str(e))
            if global_params.DEBUG_MODE:
                traceback.print_exc()
            if str(e) == "timeout":
                raise e

        execution_paths[total_no_of_paths] = current_execution_path

        solver.reset()
        solver.add(path_conditions_and_vars["path_condition"])

        if global_params.DEBUG_MODE:
            print("Branch expression: " +
                  remove_line_break_space(branch_expression))

        if not branch_expression in list_of_comparisons:
            list_of_comparisons[branch_expression] = get_function_signature_from_path_condition(
                path_conditions_and_vars["path_condition"])

        solver.add(branch_expression)

        isLeftBranchFeasible = True

        try:
            try:
                if solver.check() == unsat and not (branch_expression == True or branch_expression == False or branch_expression == Not(True) or branch_expression == Not(False)):
                    isLeftBranchFeasible = False
            except:
                isLeftBranchFeasible = False
            if not isLeftBranchFeasible:
                if not vertices[block].get_jump_target() in feasible_blocks:
                    infeasible_blocks.append(vertices[block].get_jump_target())
                if global_params.DEBUG_MODE:
                    print("LEFT BRANCH IS INFEASIBLE ("+str(solver.check())+")")
            else:
                if vertices[block].get_jump_target() in infeasible_blocks:
                    infeasible_blocks.remove(vertices[block].get_jump_target())
                    for heuristic in heuristics:
                        if heuristic["block"] == vertices[block].get_jump_target():
                            heuristics.remove(heuristic)
                feasible_blocks.append(vertices[block].get_jump_target())
            left_branch = vertices[block].get_jump_target()
            new_params = params.copy()
            new_params.depth = depth
            new_params.block = left_branch
            new_params.pre_block = block
            new_params.visited_edges = visited_edges
            new_params.global_state["pc"] = left_branch
            new_params.is_feasible = isLeftBranchFeasible
            new_params.path_conditions_and_vars["path_condition"].append(
                branch_expression)
            sym_exec_block(new_params)
        except Exception as e:
            log_file.write(str(e))
            if global_params.DEBUG_MODE:
                traceback.print_exc()
            if str(e) == "timeout":
                raise e
    else:
        updated_count_number = visited_edges[current_edge] - 1
        visited_edges.update({current_edge: updated_count_number})
        raise Exception('Unknown Jump-Type')

# Symbolically executing an instruction


def sym_exec_ins(params):
    global visited_pcs
    global solver
    global vertices
    global edges
    global source_map
    global g_timeout
    global execution_paths
    global account_balance

    if g_timeout:
        raise Exception("timeout")

    start = params.block
    instr = params.instr
    stack = params.stack
    mem = params.mem
    memory = params.memory
    global_state = params.global_state
    sha3_list = params.sha3_list
    path_conditions_and_vars = params.path_conditions_and_vars
    analysis = params.analysis
    models = params.models
    calls = params.calls
    func_call = params.func_call

    visited_pcs.add(global_state["pc"])

    instr_parts = str.split(instr, ' ')

    execution_paths[total_no_of_paths].append(global_state["pc"])

    # collecting the analysis result by calling this skeletal function
    # this should be done before symbolically executing the instruction,
    # since SE will modify the stack and mem
    update_analysis(analysis, instr_parts[0], stack, mem,
                    global_state, path_conditions_and_vars, solver)

    log.debug("==============================")
    log.debug("EXECUTING: " + instr)

    # TODO: INVALID

    #
    #  0s: Stop and Arithmetic Operations
    #
    if instr_parts[0] == "STOP":
        global_state["pc"] = global_state["pc"] + 1
        # return
    elif instr_parts[0] == "ADD":
        if len(stack) > 1:
            first = stack.pop(0)
            second = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first + second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first + second
            else:
                # both are real and we need to manually modulus with 2 ** 256
                # if both are symbolic z3 takes care of modulus automatically
                computed = (first + second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed
            if isReal(computed):
                if not global_state["pc"] in list_of_additions:
                    list_of_additions[global_state["pc"]] = []
                if not computed in list_of_additions[global_state["pc"]]:
                    list_of_additions[global_state["pc"]].append(computed)
            stack.insert(0, computed)
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MUL":
        if len(stack) > 1:
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
            computed = first * second & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            if isReal(computed):
                if not global_state["pc"] in list_of_multiplications:
                    list_of_multiplications[global_state["pc"]] = []
                if not computed in list_of_multiplications[global_state["pc"]]:
                    list_of_multiplications[global_state["pc"]].append(
                        computed)
            stack.insert(0, computed)
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SUB":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isReal(first) and isSymbolic(second):
                first = BitVecVal(first, 256)
                computed = first - second
            elif isSymbolic(first) and isReal(second):
                second = BitVecVal(second, 256)
                computed = first - second
            else:
                computed = (first - second) % (2 ** 256)
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "DIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first / second
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_solver(solver) == unsat:
                    computed = 0
                else:
                    computed = UDiv(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SDIV":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if second == 0:
                    computed = 0
                elif first == -2**255 and second == -1:
                    computed = -2**255
                else:
                    sign = -1 if (first / second) < 0 else 1
                    computed = sign * (abs(first) / abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_solver(solver) == unsat:
                    computed = 0
                else:
                    solver.push()
                    solver.add(Not(And(first == -2**255, second == -1)))
                    if check_solver(solver) == unsat:
                        computed = -2**255
                    else:
                        s = Solver()
                        s.set("timeout", global_params.TIMEOUT)
                        s.add(first / second < 0)
                        sign = -1 if check_solver(s) == sat else 1
                        def z3_abs(x): return If(x >= 0, x, -x)
                        first = z3_abs(first)
                        second = z3_abs(second)
                        computed = sign * (first / second)
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_unsigned(first)
                    second = to_unsigned(second)
                    computed = first % second & UNSIGNED_BOUND_NUMBER
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_solver(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    computed = URem(first, second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SMOD":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if second == 0:
                    computed = 0
                else:
                    first = to_signed(first)
                    second = to_signed(second)
                    sign = -1 if first < 0 else 1
                    computed = sign * (abs(first) % abs(second))
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(second == 0))
                if check_solver(solver) == unsat:
                    # it is provable that second is indeed equal to zero
                    computed = 0
                else:
                    solver.push()
                    solver.add(first < 0)  # check sign of first element
                    sign = BitVecVal(-1, 256) if check_solver(solver) == sat \
                        else BitVecVal(1, 256)
                    solver.pop()
                    def z3_abs(x): return If(x >= 0, x, -x)
                    first = z3_abs(first)
                    second = z3_abs(second)
                    computed = sign * (first % second)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "ADDMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)
            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first + second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                third = to_symbolic(third)
                solver.push()
                solver.add(Not(third == 0))
                if check_solver(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = (first + second) % third
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MULMOD":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            third = stack.pop(0)
            if isAllReal(first, second, third):
                if third == 0:
                    computed = 0
                else:
                    computed = (first * second) % third
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                third = to_symbolic(third)
                solver.push()
                solver.add(Not(third == 0))
                if check_solver(solver) == unsat:
                    computed = 0
                else:
                    first = ZeroExt(256, first)
                    second = ZeroExt(256, second)
                    third = ZeroExt(256, third)
                    computed = URem(first * second, third)
                    computed = Extract(255, 0, computed)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            instruction_object.data_out = [computed]
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "EXP":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            base = stack.pop(0)
            exponent = stack.pop(0)
            # Type conversion is needed when they are mismatched
            if isAllReal(base, exponent):
                computed = pow(base, exponent, 2**256)
            else:
                # The computed value is unknown, this is because power is
                # not supported in bit-vector theory
                new_var_name = gen.gen_arbitrary_var()
                computed = BitVec(new_var_name, 256)
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SIGNEXTEND":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    if second & (1 << signbit_index_from_right):
                        computed = second | (
                            2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & (
                            (1 << signbit_index_from_right) - 1)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(Or(first >= 32, first < 0)))
                if check_solver(solver) == unsat:
                    computed = second
                else:
                    signbit_index_from_right = 8 * first + 7
                    solver.push()
                    solver.add(second & (1 << signbit_index_from_right) == 0)
                    if check_solver(solver) == unsat:
                        computed = second | (
                            2 ** 256 - (1 << signbit_index_from_right))
                    else:
                        computed = second & (
                            (1 << signbit_index_from_right) - 1)
                    solver.pop()
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            instruction_object.data_out = [computed]
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    #  10s: Comparison and Bitwise Logic Operations
    #
    elif instr_parts[0] == "LT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(ULT(first, second), BitVecVal(
                    1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "GT":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_unsigned(first)
                second = to_unsigned(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(UGT(first, second), BitVecVal(
                    1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SLT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first < second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first < second, BitVecVal(
                    1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SGT":  # Not fully faithful to signed comparison
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                first = to_signed(first)
                second = to_signed(second)
                if first > second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first > second, BitVecVal(
                    1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "EQ":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                if first == second:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(first == second, BitVecVal(
                    1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "ISZERO":
        # Tricky: this instruction works on both boolean and integer,
        # when we have a symbolic expression, type error might occur
        # Currently handled by try and catch
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            flag = stack.pop(0)
            if isReal(flag):
                if flag == 0:
                    computed = 1
                else:
                    computed = 0
            else:
                computed = If(flag == 0, BitVecVal(1, 256), BitVecVal(0, 256))
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "AND":
        if len(stack) > 1:
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first & second
            computed = simplify(computed) if is_expr(computed) else computed
            if (isReal(first) and hex(first) == "0xff") or (isReal(second) and hex(second) == "0xff"):
                if not global_state["pc"] in list_of_vars:
                    list_of_vars[global_state["pc"]] = []
                if isReal(first) and hex(first) == "0xff":
                    list_of_vars[global_state["pc"]].append(second)
                if isReal(second) and hex(second) == "0xff":
                    list_of_vars[global_state["pc"]].append(first)
            stack.insert(0, computed)
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "OR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first | second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "XOR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = first ^ second
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "NOT":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            computed = (~first) & UNSIGNED_BOUND_NUMBER
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "BYTE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            byte_index = 32 - first - 1
            second = stack.pop(0)

            if isAllReal(first, second):
                if first >= 32 or first < 0:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
            else:
                first = to_symbolic(first)
                second = to_symbolic(second)
                solver.push()
                solver.add(Not(Or(first >= 32, first < 0)))
                if check_solver(solver) == unsat:
                    computed = 0
                else:
                    computed = second & (255 << (8 * byte_index))
                    computed = computed >> (8 * byte_index)
                solver.pop()
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')

    # TODO: SELFBALANCE, EXTCODEHASH, CHAINID, BASEFEE, CREATE2

    elif instr_parts[0] == "SHL":
        if len(stack) >= 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            computed = second << first
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')

    elif instr_parts[0] == "SHR":
        if len(stack) >= 2:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)
            if isAllReal(first, second):
                computed = (second % (1 << 256)) >> first
            else:
                computed = LShR(second, first)
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SAR":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            first = stack.pop(0)
            second = stack.pop(0)

            computed = second >> first
            computed = simplify(computed) if is_expr(computed) else computed
            stack.insert(0, computed)
        else:
            raise ValueError('STACK underflow')
    #
    # 20s: SHA3
    #
    elif instr_parts[0] == "SHA3":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            s0 = stack.pop(0)
            s1 = stack.pop(0)
            s2 = s1 - 1
            if isAllReal(s0, s1):
                data = [mem[s0+i*32] for i in range(s1/32)]
                raw_string_data = [mem[s0+i*32] for i in range(s2/32)]

                raw_string = ''
                for value in raw_string_data:
                    if is_expr(value):
                        raw_string += str(value)
                        symbolic = True
                    else:
                        raw_string += binascii.unhexlify('%064x' % value)
                input = ''
                symbolic = False
                for value in data:
                    if is_expr(value):
                        input += str(value)
                        symbolic = True
                    else:
                        input += binascii.unhexlify('%064x' % value)
                if input in sha3_list:
                    stack.insert(0, sha3_list[input])
                else:
                    if symbolic:
                        new_var_name = ""
                        for i in reversed(range(s1/32)):
                            if is_expr(mem[s0+i*32]):
                                new_var_name += str(get_vars(mem[s0+i*32])[0])
                            else:
                                new_var_name += str(mem[s0+i*32])
                            if i != 0:
                                new_var_name += "_"
                        new_var = BitVec(new_var_name, 256)
                        sha3_list[input] = new_var
                        path_conditions_and_vars[new_var_name] = new_var
                        stack.insert(0, new_var)
                    else:
                        hash = sha3.keccak_256(input).hexdigest()
                        new_var = int(hash, 16)
                        sha3_list[input] = new_var
                        hashed = {}
                        hashed["path_condition"] = path_conditions_and_vars["path_condition"]
                        hashed["function_signature"] = get_function_signature_from_path_condition(
                            hashed["path_condition"])
                        hashed["input"] = binascii.hexlify(input)
                        hashed["value"] = new_var
                        hashed["block"] = params.block
                        hashed['raw_string'] = raw_string
                        hashed["pc"] = global_state["pc"]
                        if hashed not in list_of_hashes:
                            list_of_hashes.append(hashed)
                        stack.insert(0, new_var)
            else:
                new_var_name = gen.gen_arbitrary_var()
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    #
    # 30s: Environment Information
    #
    elif instr_parts[0] == "ADDRESS":  # get address of currently executing account
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, path_conditions_and_vars["Ia"])
    elif instr_parts[0] == "BALANCE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                balance = data_source.getBalance(address)

            # else:
            #     new_var_name = gen.gen_balance_var()
            #     if new_var_name in path_conditions_and_vars:
            #         new_var = path_conditions_and_vars[new_var_name]
            #         # account_balance = new_var_name
            #     else:
            #         new_var = BitVec(new_var_name, 256)
            #         path_conditions_and_vars[new_var_name] = new_var


            else:
                new_var_name = gen.gen_balance_var(address)
                if path_conditions_and_vars["Ia"] in get_vars(address):
                    new_var_name = gen.gen_balance_var(path_conditions_and_vars["Ia"])
                    account_balance = BitVec(new_var_name, 256)
                if new_var_name in path_conditions_and_vars:
                    balance = path_conditions_and_vars[new_var_name]
                else:
                    balance = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = balance
                    if path_conditions_and_vars["Ia"] in get_vars(address):
                        path_conditions_and_vars["path_condition"].append(balance > 0)
                        # path_conditions_and_vars["path_condition"].append(balance >= 0)
                        # path_conditions_and_vars["path_condition"].append(
                        balance = balance + path_conditions_and_vars["Iv"]
            if isReal(address):
                hashed_address = "concrete_address_" + str(address)
            else:
                hashed_address = str(address)
            global_state["balance"][hashed_address] = balance
            stack.insert(0, balance)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CALLER":  # get caller address
        # that is directly responsible for this execution
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["sender_address"])
    elif instr_parts[0] == "ORIGIN":  # get execution origination address
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["origin"])

    elif instr_parts[0] == "CALLVALUE":  # get value of this transaction
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["value"])
    elif instr_parts[0] == "CALLDATALOAD":  # from input data from environment
        if len(stack) > 0:
            position = stack.pop(0)
            if isReal(position) and position != 0:
                function_signature = None
                for condition in path_conditions_and_vars["path_condition"]:
                    if is_expr(condition) and str(condition).startswith("If(Extract(255, 224, Id_1) == "):
                        match = re.compile(
                            "Extract\(255, 224, Id_1\) == ([0-9]+)").findall(str(condition))
                        if match:
                            function_signature = int(match[0])
                if not function_signature in list_of_functions:
                    list_of_functions[function_signature] = []
                calldataload = {}
                calldataload["block"] = params.block
                calldataload["pc"] = global_state["pc"]
                calldataload["position"] = position
                list_of_functions[function_signature].append(calldataload)
            # if source_map:
            #    source_code = source_map.find_source_code(global_state["pc"] - 1)
            #    if source_code.startswith("function") and isReal(position):
            #        idx1 = source_code.index("(") + 1
            #        idx2 = source_code.index(")")
            #        params_code = source_code[idx1:idx2]
            #        params_list = params_code.split(",")
            #        params_list = [param.split(" ")[-1] for param in params_list]
            #        param_idx = (position - 4) / 32
            #        new_var_name = params_list[param_idx]
            #        source_map.var_names.append(new_var_name)
            #    else:
            #    new_var_name = gen.gen_data_var(position)
            # else:
            new_var_name = gen.gen_data_var(position)
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CALLDATASIZE":
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_data_size()
        if new_var_name in path_conditions_and_vars:
            new_var = path_conditions_and_vars[new_var_name]
        else:
            new_var = BitVec(new_var_name, 256)
            path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif instr_parts[0] == "CALLDATACOPY":  # Copy input data to memory
        #  TODO: Don't know how to simulate this yet
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CODESIZE":
        if c_name.endswith('.disasm'):
            evm_file_name = c_name[:-7]
        else:
            evm_file_name = c_name
        with open(evm_file_name, 'r') as evm_file:
            evm = evm_file.read()[:-1]
            code_size = len(evm)/2
            stack.insert(0, code_size)
    elif instr_parts[0] == "CODECOPY":
        if len(stack) > 2:
            global_state["pc"] = global_state["pc"] + 1
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(mem_location, current_miu_i, code_from, no_bytes):
                if six.PY2:
                    temp = long(
                        math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(
                        math.ceil((mem_location + no_bytes) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp

                if c_name.endswith('.disasm'):
                    evm_file_name = c_name[:-7]
                else:
                    evm_file_name = c_name
                with open(evm_file_name, 'r') as evm_file:
                    evm = evm_file.read()[:-1]
                    start = code_from * 2
                    end = start + no_bytes * 2
                    code = evm[start: end]
                mem[mem_location] = int(code, 16)
            else:
                new_var_name = gen.gen_code_var("Ia", code_from, no_bytes)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                temp = ((mem_location + no_bytes) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if check_solver(solver) != unsat:
                    current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "EXTCODEHASH":
        if len(stack) >= 1:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            new_var_name = "IH_codehash"
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')

    elif instr_parts[0] == "GASPRICE":
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["gas_price"])
    elif instr_parts[0] == "EXTCODESIZE":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            if isReal(address) and global_params.USE_GLOBAL_BLOCKCHAIN:
                code = data_source.getCode(address)
                stack.insert(0, len(code)/2)
            else:
                # not handled yet
                new_var_name = gen.gen_code_size_var(address)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var
                stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "EXTCODECOPY":
        if len(stack) > 3:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            mem_location = stack.pop(0)
            code_from = stack.pop(0)
            no_bytes = stack.pop(0)
            current_miu_i = global_state["miu_i"]

            if isAllReal(address, mem_location, current_miu_i, code_from, no_bytes) and global_params.USE_GLOBAL_BLOCKCHAIN:
                if six.PY2:
                    temp = long(
                        math.ceil((mem_location + no_bytes) / float(32)))
                else:
                    temp = int(
                        math.ceil((mem_location + no_bytes) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp

                evm = data_source.getCode(address)
                start = code_from * 2
                end = start + no_bytes * 2
                code = evm[start: end]
                mem[mem_location] = int(code, 16)
            else:
                new_var_name = gen.gen_code_var(address, code_from, no_bytes)
                if new_var_name in path_conditions_and_vars:
                    new_var = path_conditions_and_vars[new_var_name]
                else:
                    new_var = BitVec(new_var_name, 256)
                    path_conditions_and_vars[new_var_name] = new_var

                temp = ((mem_location + no_bytes) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if check_solver(solver) != unsat:
                    current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem.clear()  # very conservative
                mem[str(mem_location)] = new_var
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "RETURNDATACOPY":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "RETURNDATASIZE":
        global_state["pc"] += 1
        new_var_name = gen.gen_arbitrary_var()
        new_var = BitVec(new_var_name, 256)
        stack.insert(0, new_var)
    #
    #  40s: Block Information
    #
    elif instr_parts[0] == "BLOCKHASH":  # information from block header
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            new_var_name = "IH_blockhash"
            if new_var_name in path_conditions_and_vars:
                new_var = path_conditions_and_vars[new_var_name]
            else:
                new_var = BitVec(new_var_name, 256)
                path_conditions_and_vars[new_var_name] = new_var
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "COINBASE":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentCoinbase"])
    elif instr_parts[0] == "TIMESTAMP":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentTimestamp"])
    elif instr_parts[0] == "NUMBER":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentNumber"])
    elif instr_parts[0] == "DIFFICULTY":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentDifficulty"])
    elif instr_parts[0] == "GASLIMIT":  # information from block header
        global_state["pc"] = global_state["pc"] + 1
        stack.insert(0, global_state["currentGasLimit"])
    #
    #  50s: Stack, Memory, Storage, and Flow Information
    #
    elif instr_parts[0] == "POP":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MLOAD":
        if len(stack) > 0:
            global_state["pc"] = global_state["pc"] + 1
            address = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isAllReal(address, current_miu_i) and address in mem:
                if six.PY2:
                    temp = long(math.ceil((address + 32) / float(32)))
                else:
                    temp = int(math.ceil((address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                value = mem[address]
                stack.insert(0, value)
                log.debug("temp: " + str(temp))
                log.debug("current_miu_i: " + str(current_miu_i))
            else:
                temp = ((address + 31) / 32) + 1
                current_miu_i = to_symbolic(current_miu_i)
                expression = current_miu_i < temp
                # solver.push()
                # solver.add(expression)
                # if check_solver(solver) != unsat:
                # this means that it is possibly that current_miu_i < temp
                #    current_miu_i = If(expression,temp,current_miu_i)
                # solver.pop()
                if address in mem:
                    value = mem[address]
                    stack.insert(0, value)
                else:
                    new_var_name = gen.gen_mem_var(address)
                    if not new_var_name in path_conditions_and_vars:
                        path_conditions_and_vars[new_var_name] = BitVec(
                            new_var_name, 256)
                    new_var = path_conditions_and_vars[new_var_name]
                    stack.insert(0, new_var)
                    mem[address] = new_var
                log.debug("temp: " + str(temp))
                log.debug("current_miu_i: " + str(current_miu_i))
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MSTORE":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            current_miu_i = global_state["miu_i"]
            if isReal(stored_address):
                # preparing data for hashing later
                old_size = len(memory) // 32
                new_size = ceil32(stored_address + 32) // 32
                mem_extend = (new_size - old_size) * 32
                memory.extend([0] * mem_extend)
                value = stored_value
                for i in range(31, -1, -1):
                    memory[stored_address + i] = value % 256
                    value /= 256
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 32) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 32) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                # note that the stored_value could be symbolic
                mem[stored_address] = stored_value
                log.debug("temp: " + str(temp))
                log.debug("current_miu_i: " + str(current_miu_i))
            else:
                log.debug("temp: " + str(stored_address))
                temp = ((stored_address + 31) / 32) + 1
                log.debug("current_miu_i: " + str(current_miu_i))
                expression = current_miu_i < temp
                log.debug("Expression: " + str(expression))
                # solver.push()
                # solver.add(expression)
                # if check_solver(solver) != unsat:
                # this means that it is possibly that current_miu_i < temp
                #    current_miu_i = If(expression,temp,current_miu_i)
                # solver.pop()
                # mem.clear()  # very conservative
                mem[stored_address] = stored_value
                log.debug("temp: " + str(temp))
                log.debug("current_miu_i: " + str(current_miu_i))
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "MSTORE8":
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stored_address = stack.pop(0)
            temp_value = stack.pop(0)
            stored_value = temp_value % 256  # get the least byte
            current_miu_i = global_state["miu_i"]
            if isAllReal(stored_address, current_miu_i):
                if six.PY2:
                    temp = long(math.ceil((stored_address + 1) / float(32)))
                else:
                    temp = int(math.ceil((stored_address + 1) / float(32)))
                if temp > current_miu_i:
                    current_miu_i = temp
                # note that the stored_value could be symbolic
                mem[stored_address] = stored_value
            else:
                temp = (stored_address / 32) + 1
                if isReal(current_miu_i):
                    current_miu_i = BitVecVal(current_miu_i, 256)
                expression = current_miu_i < temp
                solver.push()
                solver.add(expression)
                if check_solver(solver) != unsat:
                    # this means that it is possibly that current_miu_i < temp
                    current_miu_i = If(expression, temp, current_miu_i)
                solver.pop()
                mem[stored_address] = stored_value
                # mem.clear()  # very conservative
            global_state["miu_i"] = current_miu_i
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SLOAD":
        if len(stack) > 0:
            address = stack.pop(0)
            if is_expr(address):
                address = simplify(address)
            if address in global_state["Ia"]:
                value = global_state["Ia"][address]
                stack.insert(0, value)
            else:
                new_var_name = gen.gen_owner_store_var(address)
                if not new_var_name in path_conditions_and_vars:
                    if address.__class__.__name__ == "BitVecNumRef":
                        address = address.as_long()
                    else:
                        path_conditions_and_vars[new_var_name] = BitVec(
                            new_var_name, 256)
                new_var = path_conditions_and_vars[new_var_name]
                stack.insert(0, new_var)
                global_state["Ia"][address] = new_var
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')

    elif instr_parts[0] == "SSTORE":
        if len(stack) > 1:
            stored_address = stack.pop(0)
            stored_value = stack.pop(0)
            sstore = {}
            sstore["block"] = params.block
            sstore["pc"] = global_state["pc"]
            sstore["address"] = stored_address
            sstore["value"] = stored_value
            if stored_address in global_state["Ia"]:
                sstore["variable"] = global_state["Ia"][stored_address]
            else:
                sstore["variable"] = BitVec(
                    gen.gen_owner_store_var(stored_address), 256)
            sstore["path_condition"] = path_conditions_and_vars["path_condition"]
            sstore["function_signature"] = get_function_signature_from_path_condition(
                sstore["path_condition"])
            if not sstore in list_of_sstores:
                list_of_sstores.append(sstore)
            global_state["pc"] = global_state["pc"] + 1
            global_state["Ia"][stored_address] = stored_value
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "JUMP":
        if len(stack) > 0:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError(
                        "Target address must be an integer: "+str(target_address))
            vertices[start].set_jump_target(target_address)
            if target_address not in edges[start]:
                edges[start].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "JUMPI":
        # We need to prepare two branches
        if len(stack) > 1:
            target_address = stack.pop(0)
            if isSymbolic(target_address):
                try:
                    target_address = int(str(simplify(target_address)))
                except:
                    raise TypeError(
                        "Target address must be an integer: "+str(target_address))
            vertices[start].set_jump_target(target_address)
            flag = stack.pop(0)

            if flag.__class__.__name__ == "BitVecNumRef":
                flag = flag.as_long()

            branch_expression = (flag != 0)

            function_signature = None
            if is_expr(branch_expression) and str(branch_expression).startswith("If(Extract(255, 224, Id_1) == "):
                match = re.compile(
                    "Extract\(255, 224, Id_1\) == ([0-9]+)").findall(str(branch_expression))
                if match:
                    function_signature = int(match[0])
            if function_signature and not function_signature in list_of_functions:
                list_of_functions[function_signature] = []

            vertices[start].set_branch_expression(branch_expression)
            if target_address not in edges[start]:
                edges[start].append(target_address)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "PC":
        stack.insert(0, global_state["pc"])
        global_state["pc"] = global_state["pc"] + 1
    elif instr_parts[0] == "MSIZE":
        global_state["pc"] = global_state["pc"] + 1
        msize = 32 * global_state["miu_i"]
        stack.insert(0, msize)
    elif instr_parts[0] == "GAS":
        # In general, we do not have this precisely. It depends on both
        # the initial gas and the amount has been depleted
        # we need to think about this in the future, in case precise gas
        # can be tracked
        global_state["pc"] = global_state["pc"] + 1
        new_var_name = gen.gen_gas_var()
        new_var = BitVec(new_var_name, 256)
        path_conditions_and_vars[new_var_name] = new_var
        stack.insert(0, new_var)
    elif instr_parts[0] == "JUMPDEST":
        # Literally do nothing
        global_state["pc"] = global_state["pc"] + 1
    #
    #  60s & 70s: Push Operations
    #
    elif instr_parts[0].startswith('PUSH', 0):  # this is a push instruction
        position = int(instr_parts[0][4:], 10)
        global_state["pc"] = global_state["pc"] + 1 + position
        pushed_value = int(instr_parts[1], 16)
        stack.insert(0, pushed_value)
    #
    #  80s: Duplication Operations
    #
    elif instr_parts[0].startswith("DUP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(instr_parts[0][3:], 10) - 1
        if len(stack) > position:
            duplicate = stack[position]
            stack.insert(0, duplicate)
        else:
            raise ValueError('STACK underflow')

    #
    #  90s: Swap Operations
    #
    elif instr_parts[0].startswith("SWAP", 0):
        global_state["pc"] = global_state["pc"] + 1
        position = int(instr_parts[0][4:], 10)
        if len(stack) > position:
            temp = stack[position]
            stack[position] = stack[0]
            stack[0] = temp
        else:
            raise ValueError('STACK underflow')

    #
    #  a0s: Logging Operations
    #
    elif instr_parts[0] in ("LOG0", "LOG1", "LOG2", "LOG3", "LOG4"):
        global_state["pc"] = global_state["pc"] + 1
        # We do not simulate these log operations
        num_of_pops = 2 + int(instr_parts[0][3:])
        while num_of_pops > 0:
            stack.pop(0)
            num_of_pops -= 1

    #
    #  f0s: System Operations
    #
    elif instr_parts[0] == "CREATE":
        if len(stack) > 2:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CALL":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            call = {}
            call["path_condition"] = copy.deepcopy(
                path_conditions_and_vars["path_condition"])
            call["function_signature"] = get_function_signature_from_path_condition(
                call["path_condition"])
            call["recipient"] = recipient
            call["value"] = transfer_amount
            call["input_offset"] = start_data_input
            call["input_size"] = size_data_input
            call["memory"] = mem
            call["block"] = params.block
            call["type"] = "CALL"
            call["gas"] = outgas
            call["pc"] = global_state["pc"]
            call["id"] = len(list_of_calls)
            if not total_no_of_paths in list_of_calls:
                list_of_calls[total_no_of_paths] = []
            if call not in list_of_calls[total_no_of_paths]:
                list_of_calls[total_no_of_paths].append(call)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount) and transfer_amount == 0:
                stack.insert(0, 1)   # x = 0
            else:
                # Let us ignore the call depth
                balance_ia = global_state["balance"]["Ia"]
                is_enough_fund = (transfer_amount <= balance_ia)
                solver.push()
                solver.add(is_enough_fund)
                if check_solver(solver) == unsat:
                    # this means not enough fund, thus the execution will result in exception
                    solver.pop()
                    stack.insert(0, 0)   # x = 0
                else:
                    # the execution is possibly okay
                    stack.insert(0, 1)   # x = 1
                    solver.pop()
                    solver.add(is_enough_fund)
                    path_conditions_and_vars["path_condition"].append(
                        is_enough_fund)
                    last_idx = len(
                        path_conditions_and_vars["path_condition"]) - 1
                    analysis["time_dependency_bug"][last_idx] = global_state["pc"] - 1
                    new_balance_ia = (balance_ia - transfer_amount)

                    global_state["balance"]["Ia"] = new_balance_ia
                    address_is = path_conditions_and_vars["Is"]
                    address_is = (address_is & CONSTANT_ONES_159)
                    boolean_expression = (recipient != address_is)
                    solver.push()
                    solver.add(boolean_expression)
                    # pdb.set_trace()
                    if check_solver(solver) == unsat:
                        solver.pop()
                        new_balance_is = (
                            global_state["balance"]["Is"] + transfer_amount)
                        global_state["balance"]["Is"] = new_balance_is
                    else:
                        solver.pop()
                        if isReal(recipient):
                            new_address_name = "concrete_address_" + \
                                str(recipient)
                        else:
                            new_address_name = gen.gen_arbitrary_address_var()
                        old_balance_name = gen.gen_arbitrary_var()
                        old_balance = BitVec(old_balance_name, 256)
                        path_conditions_and_vars[old_balance_name] = old_balance
                        constraint = (old_balance >= 0)
                        solver.add(constraint)
                        path_conditions_and_vars["path_condition"].append(constraint)
                        new_balance = (old_balance + transfer_amount)
                        global_state["balance"][new_address_name] = new_balance
                        # pdb.set_trace()
            global_state["pc"] = global_state["pc"] + 1
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CALLCODE":
        # TODO: Need to handle miu_i
        if len(stack) > 6:
            global_state["pc"] = global_state["pc"] + 1
            outgas = stack.pop(0)
            stack.pop(0)  # this is not used as recipient
            transfer_amount = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            # in the paper, it is shaky when the size of data output is
            # min of stack[6] and the | o |

            if isReal(transfer_amount):
                if transfer_amount == 0:
                    stack.insert(0, 1)   # x = 0
                    return

            # Let us ignore the call depth
            balance_ia = global_state["balance"]["Ia"]
            is_enough_fund = (transfer_amount <= balance_ia)
            solver.push()
            solver.add(is_enough_fund)
            if check_solver(solver) == unsat:
                # this means not enough fund, thus the execution will result in exception
                solver.pop()
                stack.insert(0, 0)   # x = 0
            else:
                # the execution is possibly okay
                stack.insert(0, 1)   # x = 1
                solver.pop()
                solver.add(is_enough_fund)
                path_conditions_and_vars["path_condition"].append(
                    is_enough_fund)
                last_idx = len(path_conditions_and_vars["path_condition"]) - 1
                analysis["time_dependency_bug"][last_idx]
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "CREATE2":
        if len(stack) >= 4:
            global_state["pc"] += 1
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            stack.pop(0)
            new_var_name = gen.gen_arbitrary_var()
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "DELEGATECALL" or instr_parts[0] == "STATICCALL":
        if len(stack) > 5:
            global_state["pc"] += 1
            outgas = stack.pop(0)
            recipient = stack.pop(0)
            start_data_input = stack.pop(0)
            size_data_input = stack.pop(0)
            start_data_output = stack.pop(0)
            size_data_ouput = stack.pop(0)
            call = {}
            call["path_condition"] = path_conditions_and_vars["path_condition"]
            call["function_signature"] = get_function_signature_from_path_condition(
                call["path_condition"])
            call["recipient"] = recipient
            call["value"] = None
            call["input_offset"] = start_data_input
            call["input_size"] = size_data_input
            call["memory"] = mem
            call["block"] = params.block
            call["type"] = instr_parts[0]
            call["gas"] = outgas
            call["pc"] = global_state["pc"]
            call["id"] = len(list_of_calls)
            if not total_no_of_paths in list_of_calls:
                list_of_calls[total_no_of_paths] = []
            if not call in list_of_calls[total_no_of_paths]:
                list_of_calls[total_no_of_paths].append(call)
            new_var_name = gen.gen_arbitrary_var()
            new_var = BitVec(new_var_name, 256)
            stack.insert(0, new_var)
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "RETURN" or instr_parts[0] == "REVERT":
        # TODO: Need to handle miu_i
        if len(stack) > 1:
            global_state["pc"] = global_state["pc"] + 1
            stack.pop(0)
            stack.pop(0)
            pass
        else:
            raise ValueError('STACK underflow')
    elif instr_parts[0] == "SUICIDE" or instr_parts[0] == "SELFDESTRUCT":
        global suicidal
        suicidal = True
        recipient = stack.pop(0)
        transfer_amount = global_state["balance"]["Ia"]
        suicide = {}
        suicide["path_condition"] = path_conditions_and_vars["path_condition"]
        suicide["function_signature"] = get_function_signature_from_path_condition(
            suicide["path_condition"])
        suicide["recipient"] = recipient
        suicide["value"] = transfer_amount
        suicide["block"] = params.block
        suicide["pc"] = global_state["pc"]
        if suicide not in list_of_suicides:
            list_of_suicides.append(suicide)
        global_state["balance"]["Ia"] = 0
        if isReal(recipient):
            new_address_name = "concrete_address_" + str(recipient)
        else:
            new_address_name = gen.gen_arbitrary_address_var()
        old_balance_name = gen.gen_arbitrary_var()
        old_balance = BitVec(old_balance_name, 256)
        path_conditions_and_vars[old_balance_name] = old_balance
        constraint = (old_balance >= 0)
        solver.add(constraint)
        path_conditions_and_vars["path_condition"].append(constraint)
        new_balance = (old_balance + transfer_amount)
        global_state["balance"][new_address_name] = new_balance
        global_state["pc"] = global_state["pc"] + 1
    elif instr_parts[0] == "INVALID":
        pass
    elif instr_parts[0] == "ASSERTFAIL":
        pass
    else:
        print("UNKNOWN INSTRUCTION: " + instr_parts[0])
        raise Exception('UNKNOWN INSTRUCTION: ' + instr_parts[0])

    try:
        print_state(stack, mem, global_state)
    except:
        log.debug("Error: Debugging states")

def get_function_signature_from_path_condition(path_condition):
    for condition in path_condition:
        if is_expr(condition) and str(condition).startswith("If(Extract(255, 224, Id_1) == "):
            match = re.compile(
                "Extract\(255, 224, Id_1\) == ([0-9]+)").findall(str(condition))
            if match:
                return int(match[0])
    return None

# TODO: Detect if a money flow depends on the timestamp
# TODO: detect if two paths send money to different people


########################################################
#                      Heuristics                      #
########################################################

########################################################
#                  H0-0: Cash Flow 0                   #
########################################################

def detect_cash_flow_in():
    for terminal in terminals:
        if terminal["opcode"] != "REVERT":
            s = Solver()
            s.set("timeout", global_params.TIMEOUT)
            s.add(terminal["path_condition"])
            s.add(message_value > 0)
            if s.check() == sat:
                return True
    return False


def detect_cash_flow_out():
    if suicidal:
        return True
    else:
        flow_out = False
        for index in list_of_calls:
            for call in list_of_calls[index]:
                if call["type"] == "DELEGATECALL":
                    flow_out = True
                elif call["type"] == "CALL" and is_expr(call["value"]) or call["value"] > 0:
                    flow_out = True

        return flow_out
    return False


def detect_cash_flow():
    # Check if money could potentially go in
    money_flow_in = detect_cash_flow_in()

    # Check if money could potentially go out
    money_flow_out = detect_cash_flow_out()

    if money_flow_in and money_flow_out:
        heuristic = {}
        heuristic["function_signature"] = None
        heuristic["block"] = None
        heuristic["type"] = HeuristicTypes.MONEY_FLOW
        heuristic["pc"] = None
        if not heuristic in heuristics:
            heuristics.append(heuristic)
        return True
    return False

########################################################
#           H0-1: Cash Flow 1 (using owner)            #
########################################################

# there's no possibility that claim could be false
def provee(claim, *constraints, **keywords):
    s = Solver()
    s.set("timeout", global_params.TIMEOUT)
    s.set(**keywords)
    s.add(Not(claim))
    s.add(*constraints)
    if keywords.get('show', False):
        print(s)
    r = s.check()
    if r == unsat:
        return True
    else:
        return False
    print(r)

# prints all the path conditions that are related to the recipient or a specific address
def get_recipient_and_relevant_path_conds(call_or_suicide):
    r_vars = get_vars(call_or_suicide["recipient"])
    if len(r_vars) > 1:
        print("len(r_vars) > 1: %s" % r_vars)

    if r_vars:
        relevant_p_conds = []
        r_var = r_vars[0]
        for p_cond in call_or_suicide["path_condition"]:
            if expr_depends_on(p_cond, r_var):
                relevant_p_conds.append(simplify(p_cond))
    elif not r_vars:
        recipient_address = call_or_suicide["recipient"]
        relevant_p_conds = []
        for p_cond in call_or_suicide["path_condition"]:
            if re.search(str(recipient_address), str(p_cond)):
                relevant_p_conds.append(simplify(p_cond))
    return (call_or_suicide["recipient"], relevant_p_conds)


def get_recipient_and_path_conds(call_or_suicide):
    path_conditions = []
    for p_cond in call_or_suicide["path_condition"]:
        if is_expr(p_cond):
            path_conditions.append(simplify(p_cond))
        else:
            path_conditions.append(p_cond)
    return (call_or_suicide["recipient"], path_conditions, call_or_suicide["pc"])


def get_cash_flow_recipients():
    recipients = []
    global unknown_calls
    unknown_calls = []
    s = Solver()
    s.set("timeout", global_params.TIMEOUT)
    for suicide in list_of_suicides:
        s.reset()
        s.add(suicide["path_condition"])
        if s.check() == sat:
            recipients.append(get_recipient_and_path_conds(suicide))

    for index in list_of_calls:
        for call in list_of_calls[index]:
            s.reset()
            s.add(call["path_condition"])
            call_sat = s.check()
            if call_sat == unknown:
                unknown_calls.append(call["pc"])
            if call_sat == sat:

                if call["type"] == "DELEGATECALL":
                    recipients.append(get_recipient_and_path_conds(call)) 
                    continue

                calling_another_contract = not is_expr(call["value"]) and call["value"] == 0
                if calling_another_contract:
                    continue

                zero_money_transfer = is_expr(call["value"]) and provee(call["value"] == 0, call["path_condition"])
                if zero_money_transfer:
                    continue
           
                # if call["type"] == "CALL" and is_expr(call["value"]) or call["value"] > 0:
                recipients.append(get_recipient_and_path_conds(call))
    return recipients


# def find_the_owners():
#     global owners
#     global owner_aware

#     print("Constructor Variebls")
#     for sstore in constructor_variables["sstore"]:
#         s = Solver()
#         s.set("timeout", global_params.TIMEOUT)
#         s.add(sstore["path_condition"])
#         print(s.check())
#         pretty_printer.pprint(sstore)
#         print("*********************   ***********************")

#     if constructor_variables["sstore"]:
#         for con_var in constructor_variables["sstore"]:
#             if is_expr(con_var["variable"]):
#                 owner_found = provee(Extract(159, 0, con_var["variable"]) == Extract(
#                     159, 0, message_sender), con_var["variable"] == con_var["value"])
#                 if owner_found == True:
#                     owners.append(con_var["variable"])
#                     owner_aware = True

def find_the_owners():
    global owners
    global owner_aware
    owners = []
    owner_aware = False
    print("Constructor Variables")
    for sstore in constructor_variables["sstore"]:
        s = Solver()
        s.set("timeout", global_params.TIMEOUT)
        s.add(sstore["path_condition"])
        print(s.check())
        pretty_printer.pprint(sstore)
        print("*********************   ***********************")
    if constructor_variables["sstore"]:
        for con_var in constructor_variables["sstore"]:
            if is_expr(con_var["variable"]) and is_expr(con_var["value"]):
                if "Concat" in str(con_var["variable"]):
                    continue
                owner_found_by_tx_origin = provee(Extract(159, 0, con_var["value"]) == Extract(159, 0, tx_origin))
                owner_found_by_message_sender = provee(Extract(159, 0, con_var["value"]) == Extract(159, 0, message_sender))
                
                if owner_found_by_tx_origin == True or owner_found_by_message_sender == True:
                    owners.append(con_var["variable"])
                    owner_aware = True
                    print("owner found")


def ownership_can_be_changed(owner, owners_that_cant_be_changed):
    # owner = msg.sender
    # owner = new_value

    for sstore in list_of_sstores:

        if not (str(sstore["variable"]) == str(owner)):
            continue

        s = Solver()
        s.set("timeout", global_params.TIMEOUT)
        s.add(sstore["path_condition"])
        satisfiable = s.check()

        if satisfiable == unsat:
            continue

        # owner = constant value
        if isinstance(sstore["value"], (long, int)):
            continue

        # require(msg.sender == constant value)
        if satisfiable == sat:
            models = s.model()
            value = models.eval(Extract(159, 0, message_sender))
            if provee(Extract(159, 0, message_sender) == Extract(159, 0, value), sstore['path_condition']):
                continue

        # require(msg.sender == owner)
        dependent_on_owner = False
        for own in owners_that_cant_be_changed:
            dependent_on_owner = provee(Extract(159, 0, message_sender) == Extract(159, 0, own), sstore['path_condition'])
            if dependent_on_owner:
                break

        if dependent_on_owner:
            continue
        # print("ownership change!")
        return True

    return False


def owners_are_funded(recipients_and_path_conds_and_pc):
    global owners
    global sat_calls_to_owner
    global owners_that_are_funded_and_do_not_change

    unchangeable_owners = list(owners)
    print("--------------------------------------")
    print("owners", owners)
    changeable_found = True
    while(changeable_found):
        changeable_found = False
        for owner in owners:
            if owner not in unchangeable_owners:
                continue

            if ownership_can_be_changed(owner, unchangeable_owners):
                unchangeable_owners.remove(owner)
                changeable_found = True
                break

    # recipients_and_path_conds_and_pc = get_cash_flow_recipients()
    if not recipients_and_path_conds_and_pc:
        return None
    some_owner_is_funded_in_this_call = []
    for recipient_and_path_cond in recipients_and_path_conds_and_pc:
        owner_is_funded_and_can_not_be_changed = []
        recipient = recipient_and_path_cond[0]
        for owner in owners:
            owner_funded = False

            # 4 States in which the owner is funded:
            #   1. transfer(Real Address)
            #   2. transfer(Owner Address)
            #   3. require(Is == Real Address)
            #   4. require(Is == Owner Address)

            # 1.
            # owner_address = 0x7a617c2B05d2A74Ff9bABC9d81E5225C1e01004b
            # transfer_to_real_address = False
            if isinstance(recipient, long) or isinstance(recipient, int):
                # transfer_to_real_address = True
                owner_funded = True
                print("constant address", recipient_and_path_cond[2])

            # 2. owner.transfer(balance)
            if not owner_funded:
                # transfer_owner_address = False
                if is_expr(recipient):
                    owner_funded = provee(Extract(159, 0, recipient) == Extract(159, 0, owner), recipient_and_path_cond[1])
                    if owner_funded:
                        print("owner funded directly", recipient_and_path_cond[2])

            # 3. require(msg.sender == owner)
            if not owner_funded:
                owner_funded = provee(Extract(159, 0, message_sender) == Extract(159, 0, owner), recipient_and_path_cond[1])
                if owner_funded:
                    print("require(msg.sender == owner)", recipient_and_path_cond[2])

            # 4.
            # Extract(159, 0, Is) == 698670862888103124090043688033161627232733560907
            # require(Is == Real Address)
            if not owner_funded:
                s = Solver()
                s.set("timeout", global_params.TIMEOUT)
                s.add(recipient_and_path_cond[1])
                if is_expr(recipient) and s.check() == sat:
                    models = s.model()
                    value = models.eval(recipient)
                    owner_funded = provee(Extract(159, 0, message_sender) == Extract(159, 0, value), recipient_and_path_cond[1])
                    if owner_funded:
                        print("require(Is == Real Address)", recipient_and_path_cond[2])

            if owner_funded == True:
                owner_changed = ownership_can_be_changed(owner, unchangeable_owners)
            else:
                owner_changed = False
            print("owner changed?", owner, owner_changed)
            if owner_funded == True and owner_changed == False:
                owner_is_funded_and_can_not_be_changed.append(True)
                owners_that_are_funded_and_do_not_change.append(owner)
            else:
                owner_is_funded_and_can_not_be_changed.append(False)

        if any(owner_is_funded_and_can_not_be_changed):
            some_owner_is_funded_in_this_call.append(True)
            sat_calls_to_owner.append(recipient_and_path_cond[2])
        else:
            some_owner_is_funded_in_this_call.append(False)

    if all(some_owner_is_funded_in_this_call):
        return True
    return False



def detect_cash_flow_to_owner():
    # return False
    # global source_map
    global sat_calls_to_owner
    sat_calls_to_owner = []
    global owners
    global owners_that_are_funded_and_do_not_change
    owners_that_are_funded_and_do_not_change = []

    # print("list of sstores")
    # pretty_printer.pprint(list_of_sstores)

    # for sstore in list_of_sstores:
    #     print("---------------------------------------------------")
    #     s = Solver()
    #     s.set("timeout", global_params.TIMEOUT)
    #     s.add(sstore["path_condition"])
    #     if source_map:
    #         print(source_map.find_source_code(sstore["pc"]))
    #     print(s.check())
    #     pretty_printer.pprint(sstore)

    for sstore in list_of_sstores:
        for owner in owners:
            owner_require_store = provee(Extract(159, 0, message_sender) == Extract(159, 0, owner), sstore["path_condition"])
            if owner_require_store:
                print("***************-----------------**************")
                print("dependent sstore found!")
                pretty_printer.pprint(sstore)

    # for suicide in list_of_suicides:
    #     print("***************************************************")
    #     if source_map:
    #         print(source_map.find_source_code(suicide["pc"]))
    #     s = Solver()
    #     s.set("timeout", global_params.TIMEOUT)
    #     s.add(suicide["path_condition"])
    #     print(s.check())
    #     pretty_printer.pprint(suicide)

    # for index in list_of_calls:
    #     for call in list_of_calls[index]:
    #         print("***************************************************")
    #         if source_map:
    #             print(source_map.find_source_code(call["pc"]))
    #         s = Solver()
    #         s.set("timeout", global_params.TIMEOUT)
    #         s.add(call["value"] > 0)
    #         s.add(call["path_condition"])
    #         print(s.check())
    #         # pretty_printer.pprint(call)
    #         print(call["pc"])
    #         for cond in call["path_condition"]:
    #             if is_expr(cond):
    #                 print(simplify(cond))
    #         print("value", call["value"])
    #         print("recipient", call["recipient"])
    if owner_aware:
        results["owner_aware"] = True
    if owner_aware and owners_are_funded(get_cash_flow_recipients()):
        heuristic = {}
        heuristic["function_signature"] = None
        heuristic["block"] = None
        heuristic["type"] = HeuristicTypes.MONEY_FLOW_TO_OWNER
        heuristic["pc"] = None
        if not heuristic in heuristics:
            heuristics.append(heuristic)
        return True
    return False

def is_payable(call_or_suicide_or_sstore):
    for cond in call_or_suicide_or_sstore["path_condition"]:
        if is_expr(cond) and all(str(v) == "Iv" for v in get_vars(cond)):
            simplified_cond = simplify(cond)
            if str(simplified_cond) == "Iv == 0" or str(simplified_cond) == "0 == Iv":
                return False
    return True


def detect_fake_ownerchange_trick():
    global source_map
    global owners
    global sat_calls_to_owner
    global owners_that_are_funded_and_do_not_change
    print("owners_that_are_funded_and_do_not_change", owners_that_are_funded_and_do_not_change)
    
    for sstore in list_of_sstores:
        # new_owner = msg.sender
        if not is_payable(sstore):
                continue
        if is_expr(sstore["value"]) and provee(Extract(159, 0, sstore["value"]) == Extract(159, 0, message_sender), sstore["path_condition"]):
            if not sstore["value"] in owners_that_are_funded_and_do_not_change:
                for index in list_of_calls:
                    for call in list_of_calls[index]:
                        for owner in owners:
                            owner_dependent = provee(Extract(159, 0, message_sender) == Extract(159, 0, owner), call["path_condition"])
                            if owner_dependent:
                    # heuristic = {}
                    # heuristic["function_signature"] = None
                    # heuristic["block"] = None
                    # heuristic["type"] = HeuristicTypes.FAKE_OWNERCHANGE_TRICK
                    # heuristic["pc"] = None
                    # if not heuristic in heuristics:
                    #     heuristics.append(heuristic)
                                # print(source_map.find_source_code(sstore["pc"]))
                                pretty_printer.pprint(sstore)
                                heuristic = {}
                                heuristic["function_signature"] = None
                                heuristic["block"] = None
                                heuristic["type"] = HeuristicTypes.FAKE_OWNERCHANGE_TRICK
                                heuristic["pc"] = None
                                if not heuristic in heuristics:
                                    heuristics.append(heuristic)
                                results["owner_trick_test"] = True

    for owner in owners:
        for sstore in list_of_sstores:
            if not is_payable(sstore):
                continue

            # owner = msg.sender
            # means it has been tried to change the owner of the contract but that owner is not changeable and gets all of the money
            if str(sstore['variable']) == str(owner) and (owner in owners_that_are_funded_and_do_not_change):
                print("foundd!")
                # print(source_map.find_source_code(sstore["pc"]))
                pretty_printer.pprint(sstore)
                heuristic = {}
                heuristic["function_signature"] = None
                heuristic["block"] = None
                heuristic["type"] = HeuristicTypes.FAKE_OWNERCHANGE_TRICK
                heuristic["pc"] = None
                if not heuristic in heuristics:
                    heuristics.append(heuristic)


def detect_fake_call_trick():
    global unknown_calls
    payable_call_trick = False
    payable_suicide_trick = False
    global sat_calls_to_owner
    for suicide in list_of_suicides:
        if sat_calls_to_owner and suicide["pc"] not in sat_calls_to_owner:
            if not is_payable(suicide):
                continue
            heuristic = {}
            heuristic["function_signature"] = None
            heuristic["block"] = None
            heuristic["type"] = HeuristicTypes.FAKE_CALL_TRICK
            heuristic["pc"] = None
            if not heuristic in heuristics:
                heuristics.append(heuristic)
            # payable_suicide_trick = True 


    print("calls to owner",sat_calls_to_owner)
    for index in list_of_calls:
        for call in list_of_calls[index]:
            if call["pc"] in unknown_calls:
                continue

            # either: unsatisfiable call / calling another smart contract / sending 0 ethers
            if sat_calls_to_owner and call["pc"] not in sat_calls_to_owner:
                if not is_payable(call):
                    continue
                if is_expr(call["recipient"]) and not str(call["recipient"]) == "0":
                    calling_another_contract = (not is_expr(call["value"])) and (call["value"] == 0)
                    if not calling_another_contract:
                        print("one unsat or zero money transfer!", call["pc"])
                        payable_call_trick = True
                        call_to_owner = False

                        # unsat call : owner.transfer()
                        recipient = get_vars(call["recipient"])
                        for owner in owners:
                            if str(owner) in str(recipient):
                                call_to_owner = True
                                break

                        # unsat call : msg.sender.transfer()  (require msg.sender == owner)
                        # unsat call : msg.sender.transfer()  (require msg.sender == Real Address)
                        for owner in owners:
                            if not call_to_owner:
                                for condition in call["path_condition"]:
                                    if is_expr(condition) and "==" in str(condition):
                                        separated_condition = remove_line_break_space(simplify(condition)).split("==")
                                        if (str(owner) in separated_condition[0] and "Is" in separated_condition[1]) or(str(owner) in separated_condition[1] and "Is" in separated_condition[0]):
                                            call_to_owner = provee(Extract(159, 0, message_sender) == Extract(159, 0, owner), condition)
                                            break
                                        if (not "I" in separated_condition[0] and "Is" in separated_condition[1]) or(not "I" in separated_condition[1] and "Is" in separated_condition[0]):
                                            call_to_owner = True
                                            break
                        

                        if (not call_to_owner and payable_call_trick == True):
                            print("found", call["pc"])
                            heuristic = {}
                            heuristic["function_signature"] = None
                            heuristic["block"] = None
                            heuristic["type"] = HeuristicTypes.FAKE_CALL_TRICK
                            heuristic["pc"] = None
                            if not heuristic in heuristics:
                                heuristics.append(heuristic)


########################################################
#             H9: Map Key Encoding Trick               #
########################################################


# pip install --upgrade pip
# pip install unidecode

# This function finds all the map keys used in a call(recipient, value, path_condition)
def the_map_key_used_in_call(call, hash):
    map_key_address = "Ia_store_" + str(hash['value'])
    for condition in call['path_condition']:
        if not is_expr(condition):
            break
        if is_in_expr(str(map_key_address), condition):
            return hash['raw_string'].rstrip('\x00')
    if is_expr(call['value']):
        if is_in_expr(str(map_key_address), call['value']):
            return hash['raw_string'].rstrip('\x00')
    if is_expr(call['recipient']):
        if is_in_expr(str(map_key_address), call['recipient']):
            return hash['raw_string'].rstrip('\x00')
    return None


def detect_map_key_encoding():
    pass
    # all_hashes = []
    # all_sstores = []
    # map_key_list = []
    # # adds the hashes and sstores in the constructor to the listofhashes and listofsstores
    # for hash in constructor_variables["hash"]:
    #     all_hashes.append(hash)
    # for hash in list_of_hashes:
    #     all_hashes.append(hash)
    # for sstore in constructor_variables["sstore"]:
    #     all_sstores.append(sstore)
    # for sstore in list_of_sstores:
    #     all_sstores.append(sstore)

    # pretty_printer.pprint(all_hashes)

    # # finds all the sstores that are using a hash
    # for sstore in all_sstores:
    #     for hash in all_hashes:
    #         if hash["value"] == sstore["address"]:
    #             encoded_string = hash['raw_string'].rstrip('\x00')
    #             map_key_list.append(encoded_string)
    # for index in list_of_calls:
    #     for call in list_of_calls[index]:
    #         for hash in all_hashes:
    #             map_key_in_call = the_map_key_used_in_call(call, hash)
    #             if not map_key_in_call:
    #                 continue
    #             print("map key in call", map_key_in_call)
    #             map_key_in_call = unicode(map_key_in_call, "utf-8", errors='replace')
    #             print("unicode map key in call", map_key_in_call)
    #             decoded_map_key_in_call = unidecode(map_key_in_call)
    #             print("unidecode map key in call", decoded_map_key_in_call)
    #             for map_key in map_key_list:
    #                 map_key = unicode(map_key, "utf-8", errors='replace')
    #                 decoded_map_key = unidecode(map_key)
    #                 if map_key != map_key_in_call and decoded_map_key == decoded_map_key_in_call:
    #                     heuristic = {}
    #                     heuristic["function_signature"] = call["function_signature"]
    #                     heuristic["block"] = call["function_signature"]
    #                     heuristic["type"] = HeuristicTypes.MAP_KEY_ENCODING
    #                     heuristic["pc"] = call["function_signature"]
    #                     if not heuristic in heuristics:
    #                         heuristics.append(heuristic)

########################################################
#               H11: Racing Time                       #
########################################################

def detect_racing_time():
    global sat_calls_to_owner
    global owners_that_are_funded_and_do_not_change

# the minimum amount of time to do a tx in ethereum is considered to be 5 mins
    for index in list_of_calls:
        for call in list_of_calls[index]:

            if owner_aware and sat_calls_to_owner and owners_that_are_funded_and_do_not_change:
                if call["pc"] in sat_calls_to_owner and is_expr(call["recipient"]):
                    for owner in owners_that_are_funded_and_do_not_change:
                        unchangeable_owner = provee(Extract(159, 0, call["recipient"]) == Extract(159, 0, owner))
                        if unchangeable_owner:
                            continue
            
            # no_time = False
            little_time = False
            condition_args = []
            comp_args_lt = []
            comp_args_gt = []
            rct_possible = False
            for condition in call["path_condition"]:
                if is_expr(condition):
                    # find condition that has a comparison for TIMESTAMP
                    if "IH_s" in str(condition) and condition in list_of_comparisons:
                        # find the same variables in constructor and path_condition
                        # substitute the arguments in ULE with the value of the variable in the constructor
                        for con_var in constructor_variables["sstore"]:
                            for var in get_vars(condition):
                                if str(var) == str(con_var['variable']):
                                    if not is_expr(con_var['value']):
                                        condition = substitute(condition, (var, BitVecVal(con_var['value'], 256)))
                                    else:
                                        condition = substitute(condition, (var, con_var['value']))                
                        simplified_condition = simplify(condition)

                        expr_args = get_ULE_expr_args(simplified_condition)
                        condition_args.append(expr_args)
            while condition_args:
                # print("condition args", condition_args)
                args = condition_args.pop()
                if args:
                    args = args.pop()
                    if is_in_expr('IH_s', args[0]):
                        comp_args_gt.append(args[1])
                    else:
                        comp_args_lt.append(args[0])
            minimum = bv_min(comp_args_gt)
            maximum = bv_max(comp_args_lt)
            print("minimum", minimum, type(minimum))
            print("maximum", maximum, type(maximum))

            if is_expr(maximum) and is_expr(minimum) and str(maximum) != str(minimum):
                vars_in_min = get_vars(minimum)
                vars_in_max = get_vars(maximum)
                s = Solver()
                s.set("timeout", global_params.TIMEOUT)
                s.add(call["path_condition"])
                if s.check() == sat:
                    if is_expr(maximum) and is_expr(minimum) and str(maximum) != str(minimum):
                        vars_in_min = get_vars(minimum)
                        vars_in_max = get_vars(maximum)
                    if vars_in_min and vars_in_max:
                        if collections.Counter(vars_in_min) == collections.Counter(vars_in_max):
                            rct_possible = True
                    elif not (vars_in_min and vars_in_max):
                        rct_possible = True
                    # if rct_possible == True and provee(ULE((minimum - maximum), 300), minimum > maximum, *call["path_condition"]) == True:
                    #     rct_possible = True
                    elif provee(ULE((minimum - maximum), 300), minimum > maximum, *call["path_condition"]) == True:
                        rct_possible = True

            s = Solver()
            s.set("timeout", global_params.TIMEOUT)
            s.add(call["path_condition"])
            if s.check() == sat:
                # print("simpified condition", simplified_condition)
                # if (minimum == None and maximum != None) or (maximum == None and minimum != None):
                # if not provee(simplified_condition, timestamp > 0):
                #     no_time = True
                #     print("No time!")

                # x + y < IH_s < x
                # x < now < 1002
                if is_expr(maximum) and is_expr(minimum) and str(maximum) != str(minimum):
                    vars_in_min = get_vars(minimum)
                    vars_in_max = get_vars(maximum)
    
                    if vars_in_min and vars_in_max:
                        # print("min", vars_in_min)
                        # print("max", vars_in_max)
                        # TODO: What is this? -><-
                        # x + y < IH_s < x
                        if collections.Counter(vars_in_min) == collections.Counter(vars_in_max):
                            rct_possible = True
                    else:
                        rct_possible = True

                if rct_possible == True and provee(ULE((minimum - maximum), 300), minimum > maximum, *call["path_condition"]) == True:
                    little_time = True
                    print("little time")
            print("-----------------------------------")
            if little_time:
                heuristic = {}
                heuristic["function_signature"] = call["function_signature"]
                heuristic["block"] = call["block"]
                heuristic["type"] = HeuristicTypes.RACING_TIME
                heuristic["pc"] = call["pc"]
                if not heuristic in heuristics:
                    heuristics.append(heuristic)

# ULE, UGT, UGE, ULT


def detect_honeypots():
    if detect_cash_flow():
        if global_params.DEBUG_MODE:
            log.info("\t--------- Begin Time ---------")
            start_time = time.time()

        if detect_cash_flow_to_owner():
            if global_params.DEBUG_MODE:
                elapsed_time = time.time() - start_time
                log.info("\t Money flow to owner: \t " +
                        str(math.ceil(elapsed_time))+" seconds")
                start_time = time.time()
                
            detect_fake_ownerchange_trick()
            if global_params.DEBUG_MODE:
                elapsed_time = time.time() - start_time
                log.info("\t Fake ownerchange trick: \t " +
                        str(math.ceil(elapsed_time))+" seconds")
                start_time = time.time()
                
            detect_fake_call_trick()
            if global_params.DEBUG_MODE:
                elapsed_time = time.time() - start_time
                log.info("\t Fake call trick: \t " +
                        str(math.ceil(elapsed_time))+" seconds")
                start_time = time.time()

        detect_map_key_encoding()
        if global_params.DEBUG_MODE:
            elapsed_time = time.time() - start_time
            log.info("\t Map key encoding: \t " +
                     str(math.ceil(elapsed_time))+" seconds")
            start_time = time.time()

        detect_racing_time()
        if global_params.DEBUG_MODE:
            elapsed_time = time.time() - start_time
            log.info("\t Racing time: \t " +
                     str(math.ceil(elapsed_time))+" seconds")
            log.info("\t---------- End Time ----------")


    money_flow_found = any(
        [HeuristicTypes.MONEY_FLOW in heuristic["type"] for heuristic in heuristics])
    money_flow_to_owner_found = any(
        [HeuristicTypes.MONEY_FLOW_TO_OWNER in heuristic["type"] for heuristic in heuristics])
    fake_ownerchange_trick_found = any(
        [HeuristicTypes.FAKE_OWNERCHANGE_TRICK in heuristic["type"] for heuristic in heuristics])
    fake_call_trick_found = any(
        [HeuristicTypes.FAKE_CALL_TRICK in heuristic["type"] for heuristic in heuristics])
    
    map_key_encoding_found = any(
        [HeuristicTypes.MAP_KEY_ENCODING in heuristic["type"] for heuristic in heuristics])
    racing_time_found = any(
        [HeuristicTypes.RACING_TIME in heuristic["type"] for heuristic in heuristics])

    if source_map:
        # Money flow
        results["money_flow"] = money_flow_found
        s = "\t Money flow:    \t "+str(money_flow_found)
        log.info(s)
        # Money flow to owner
        pcs = [heuristic["pc"]
               for heuristic in heuristics if HeuristicTypes.MONEY_FLOW_TO_OWNER in heuristic["type"]]
        pcs = [pc for pc in pcs if source_map.find_source_code(pc)]
        pcs = source_map.reduce_same_position_pcs(pcs)
        s = source_map.to_str(pcs, "Money flow to owner")
        if s:
            results["money_flow_to_owner"] = s
        s = "\t Money flow to owner: \t "+str(money_flow_to_owner_found) + s
        log.info(s)
        # Fake ownerchange trick
        pcs = [heuristic["pc"]
               for heuristic in heuristics if HeuristicTypes.FAKE_OWNERCHANGE_TRICK in heuristic["type"]]
        pcs = [pc for pc in pcs if source_map.find_source_code(pc)]
        pcs = source_map.reduce_same_position_pcs(pcs)
        s = source_map.to_str(pcs, "Fake ownerchange trick")
        if s:
            results["fake_ownerchange_trick"] = s
        s = "\t Fake ownerchange trick: \t "+str(fake_ownerchange_trick_found) + s
        log.info(s)
        # Fake call trick
        pcs = [heuristic["pc"]
               for heuristic in heuristics if HeuristicTypes.FAKE_CALL_TRICK in heuristic["type"]]
        pcs = [pc for pc in pcs if source_map.find_source_code(pc)]
        pcs = source_map.reduce_same_position_pcs(pcs)
        s = source_map.to_str(pcs, "Fake call trick")
        if s:
            results["fake_call_trick"] = s
        s = "\t Fake call trick: \t "+str(fake_call_trick_found) + s
        log.info(s)

        # Map key encoding
        pcs = [heuristic["pc"]
               for heuristic in heuristics if HeuristicTypes.MAP_KEY_ENCODING in heuristic["type"]]
        pcs = [pc for pc in pcs if source_map.find_source_code(pc)]
        pcs = source_map.reduce_same_position_pcs(pcs)
        s = source_map.to_str(pcs, "Map key encoding")
        if s:
            results["map_key_encoding"] = s
        s = "\t Map key encoding: \t " + \
            str(map_key_encoding_found) + s
        log.info(s)
        # Racing Time
        pcs = [heuristic["pc"]
               for heuristic in heuristics if HeuristicTypes.RACING_TIME in heuristic["type"]]
        pcs = [pc for pc in pcs if source_map.find_source_code(pc)]
        pcs = source_map.reduce_same_position_pcs(pcs)
        s = source_map.to_str(pcs, "Racing time")
        if s:
            results["racing_time"] = s
        s = "\t Racing time: \t "+str(racing_time_found) + s
        log.info(s)
    else:
        # Money flow
        results["money_flow"] = money_flow_found
        s = "\t Money flow:    \t "+str(money_flow_found)
        log.info(s)
        # Money flow to owner
        results["money_flow_to_owner"] = money_flow_to_owner_found
        s = "\t Money flow to owner: \t "+str(money_flow_to_owner_found)
        log.info(s)
        # Fake ownerchange trick
        results["fake_ownerchange_trick"] = fake_ownerchange_trick_found
        s = "\t Fake ownerchange trick: \t "+str(fake_ownerchange_trick_found)
        log.info(s)
        # Fake call trick
        results["fake_call_trick"] = fake_call_trick_found
        s = "\t Fake call trick: \t "+str(fake_call_trick_found)
        log.info(s)
        # Map key encoding trick
        results["map_key_encoding"] = map_key_encoding_found
        s = "\t Map key encoding: \t "+str(map_key_encoding_found)
        log.info(s)
        # Racing time
        results["racing_time"] = racing_time_found
        s = "\t Racing time: \t "+str(racing_time_found)
        log.info(s)


class Timeout:
    #    """Timeout class using ALARM signal."""
    def __init__(self, handler, sec=10, error_message=os.strerror(errno.ETIME)):
        self.sec = sec
        self.error_message = error_message
        self.handler = handler

    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handler)
        signal.alarm(self.sec)

    def __exit__(self, *args):
        signal.alarm(0)    # disable alarm


def handler(signum, frame):
    global g_timeout
    six.print_("!!! SYMBOLIC EXECUTION TIMEOUT !!!")
    g_timeout = True
    raise Exception("timeout")

def heuristic_timeout_handler(signum, frame):
    global h_timeout
    six.print_("!!! TIMEOUT IN THE HEURISTIC !!!")
    h_timeout = True
    raise Exception("timeout")

def detect_bugs():
    global results
    global g_timeout
    global h_timeout
    global source_map
    global visited_pcs

    if global_params.DEBUG_MODE:
        six.print_("Number of total paths: "+str(total_no_of_paths))
        six.print_("")

    if instructions:
        evm_code_coverage = float(len(visited_pcs)) / \
            len(instructions.keys()) * 100
        log.info("\t EVM code coverage: \t %s%%", round(evm_code_coverage, 1))
        results["evm_code_coverage"] = str(round(evm_code_coverage, 1))

        dead_code = list(set(instructions.keys()) - set(visited_pcs))
        for pc in dead_code:
            results["dead_code"].append(instructions[pc])

        try:
            with Timeout(handler=heuristic_timeout_handler, sec=600):
                detect_honeypots()
                stop_time = time.time()
                results["execution_time"] = str(stop_time-start_time)
                log.info("\t --- "+str(stop_time - start_time)+" seconds ---")
                results["execution_paths"] = str(total_no_of_paths)
                results["timeout"] = g_timeout
                results["h_timeout"] = h_timeout
                log.debug('Done Analysing')
        except Exception as e:
            if global_params.DEBUG_MODE:
                traceback.print_exc()
            print("error", e)
            stop_time = time.time()
            results["execution_time"] = str(stop_time-start_time)
            log.info("\t --- "+str(stop_time - start_time)+" seconds ---")
            results["timeout"] = g_timeout
            results["h_timeout"] = h_timeout
            results["execution_paths"] = str(total_no_of_paths)
            if str(e) == "timeout":
                pass
            else:
                results["errors"] = str(e)
                # results["errors"] = traceback.format_exc()

    else:
        log.info("\t EVM code coverage: \t 0.0")
        log.info("\t Money flow: \t False")
        log.info("\t Money flow to owner: \t False")
        log.info("\t Fake ownerchange trick: \t False")
        log.info("\t Fake call: \t False")
        log.info("\t Map key encoding: \t False")
        log.info("\t Racing time:       \t False")
        log.info("\t  --- 0.0 seconds ---")
        results["evm_code_coverage"] = "0.0"
        results["execution_paths"] = str(total_no_of_paths)
        results["timeout"] = g_timeout
        results["h_timeout"] = h_timeout
    if len(heuristics) > 0:
        for heuristic in heuristics:
            if heuristic["function_signature"]:
                if heuristic["function_signature"]:
                    method = "{0:#0{1}x}".format(
                        heuristic["function_signature"], 10)
                else:
                    method = ""
                if not method in results["attack_methods"]:
                    results["attack_methods"].append(method)
        for index in list_of_calls:
            for call in list_of_calls[index]:
                if call["type"] == "CALL" and call["input_size"] == 0:
                    if call["function_signature"]:
                        method = "{0:#0{1}x}".format(
                            call["function_signature"], 10)
                    else:
                        method = ""
                    if not method in results["cashout_methods"]:
                        results["cashout_methods"].append(method)


def closing_message():
    global c_name
    global results

    log.info("\t====== Analysis Completed ======")
    if global_params.STORE_RESULT:
        contract_name = c_name.replace('.bin.evm.disasm', '').split('/')[-1]
        if len(str(contract_name)) == 66:
            with open('../contracts.csv', 'r') as f:
                reader = csv.DictReader(f)
                for row in reader:
                    if row["Transaction Hash"] == contract_name:
                        contract_name = row["Contract Address"]
                        c_name = contract_name
                        break
        result_file = os.path.join(
            global_params.RESULTS_DIR, c_name+'.json'.split('/')[-1])
        if '.sol' in c_name:
            result_file = os.path.join(global_params.RESULTS_DIR, c_name.split(':')[
                                       0].replace('.sol', '.json').split('/')[-1])
        elif '.bin.evm.disasm' in c_name:
            result_file = os.path.join(global_params.RESULTS_DIR, c_name.replace(
                '.bin.evm.disasm', '.json').split('/')[-1])
        mode = 'a'
        if global_params.BYTECODE:
            mode = 'w'
        if not os.path.isfile(result_file):
            with open(result_file, mode) as of:
                if ':' in c_name:
                    of.write("{")
                    of.write('"'+str(c_name.split(':')
                             [1].replace('.evm.disasm', ''))+'":')
                of.write(json.dumps(results, indent=1))
        else:
            open(result_file, 'w').close()
            with open(result_file, mode) as of:
                if ':' in c_name:
                    of.write("{")
                    of.write('"'+str(c_name.split(':')
                             [1].replace('.evm.disasm', ''))+'":')
                of.write(json.dumps(results, indent=1))


def analyze_constructor_variables(contract, contract_sol, _source_map=None):
    global c_name
    global c_name_sol
    global source_map
    global start_time
    global log_file
    global constructor_variables
    global is_constructor
    global owners
    global owner_aware
    constructor_variables = {}
    owners = []
    owner_aware = False
    c_name = contract
    c_name_sol = contract_sol
    source_map = _source_map
    is_constructor = True
    initGlobalVars()

    set_cur_file(c_name[4:] if len(c_name) > 5 else c_name)
    start_time = time.time()

    try:
        with Timeout(handler=handler, sec=global_params.GLOBAL_TIMEOUT):
            build_cfg_and_analyze()
        log.debug('Done Symbolic execution')
    except Exception as e:
        if global_params.DEBUG_MODE:
            traceback.print_exc()
        if str(e) == "timeout":
            pass
        else:
            pass

    log_file.close()

    if not "sstore" in constructor_variables:
        constructor_variables["sstore"] = []
    for sstore in list_of_sstores:
        if sstore not in constructor_variables["sstore"]:
            constructor_variables["sstore"].append(sstore)

    if not "hash" in constructor_variables:
        constructor_variables["hash"] = []
    for hash in list_of_hashes:
        if hash not in constructor_variables["hash"]:
            constructor_variables["hash"].append(hash)

    find_the_owners()


def main(solidity_version, contract, contract_sol, constructor_bytecode_found, _source_map=None):
    global c_name
    global c_name_sol
    global source_map
    global start_time
    global is_constructor
    c_name = contract
    c_name_sol = contract_sol
    source_map = _source_map
    is_constructor = False
    initGlobalVars()
    results["solidity_version"] = solidity_version
    # if solidity_version == "= 4" or solidity_version == ">= 4":
    if constructor_bytecode_found == True:
        results["constructor_found"] = True
    set_cur_file(c_name[4:] if len(c_name) > 5 else c_name)
    start_time = time.time()

    log.info("Running, please wait...")

    try:
        with Timeout(handler=handler, sec=global_params.GLOBAL_TIMEOUT):
            build_cfg_and_analyze()
        log.debug('Done Symbolic execution')
    except Exception as e:
        if global_params.DEBUG_MODE:
            traceback.print_exc()
        if str(e) == "timeout":
            pass
        else:
            pass

    log.info("\t============ Results ===========")

    detect_bugs()
    closing_message()


if __name__ == '__main__':
    main(sys.argv[1])
