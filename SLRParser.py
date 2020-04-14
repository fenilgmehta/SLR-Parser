#!/usr/bin/python3
from typing import Set, List, Union, Dict, Tuple

from graphviz import Digraph


# -----------------------------------------------------------------------------------------

def parse_grammar(file_name: str) -> Tuple[
    Dict[str, List[List[str]]],
    List[List[Union[str, List[str]]]],
    str,
    List[str],
    List[str],
    List[str]
]:
    # Grammar where lhs is key and rhs is list of productions
    G_prime: Dict[str, List[List[str]]] = {}  # Dict[str, Union[List[List[str]], list]]
    # Grammar where index of the production is used for writing reduce operations
    G_indexed: List[List[Union[str, List[str]]]] = [['', '']]  # List[Union[List[str], List[Union[str, List[str]]]]]
    start: str = ''
    terminals: Set[str] = set([])
    nonterminals: Set[str] = set([])

    # Open and read the grammar file
    with open(file_name) as grammar_file:
        # filter ensure blank lines are discarded
        grammar = list(filter(None, grammar_file.read().splitlines()))

    for g in grammar:
        head, _, prods = g.partition(' -> ')
        prods = [prod.split() for prod in ' '.join(prods.split()).split('|')]
        # prods = [prod.split() for prod in prods.split('|')]

        if not start:  # If first production, then make the grammar Augmented Grammar
            start = f"{head}'"  # Create augmented production
            G_prime[start] = [[head]]
        if head not in G_prime:
            G_prime[head] = []
            nonterminals.add(head)
        for prod in prods:
            G_prime[head].append(prod)
            G_indexed.append([head, prod])
            for symbol in prod:
                if not symbol.isupper() and symbol != '^':  # ^ denotes epsilon, i.e. empty string
                    terminals.add(symbol)
                elif symbol.isupper():
                    nonterminals.add(symbol)
                # else:  # This else will be executed if the symbol is '^', i.e. epsilon = empty string
                #     print(f"WARNING: check the symbol = '{symbol}'")

    return G_prime, G_indexed, start, list(terminals), list(nonterminals), list(terminals | nonterminals)


# -----------------------------------------------------------------------------------------

first_seen: List[str] = []


def FIRST(X: str) -> Set[str]:
    global global_terminals
    if X in global_terminals:  # CASE 1
        return {X}
    else:
        global first_seen, global_G_prime
        first = set()

        while True:
            first_seen.append(X)
            first_len = len(first)
            for prod in global_G_prime[X]:  # Grammar Productions: Dict[str, List[List[str]]], prod: List[str]
                if prod != ['^']:  # CASE 2  # `^` is empty string, i.e. Epsilon
                    for symbol in prod:
                        if symbol == X and '^' in first:
                            continue
                        if symbol in first_seen:
                            break
                        symbol_first: Set[str] = FIRST(symbol)
                        first = first | (symbol_first - set('^'))
                        if '^' not in symbol_first:
                            break
                        first.add('^')  # TODO: check if this is right or wrong
                else:  # CASE 3
                    first.add('^')
            first_seen.remove(X)
            if first_len == len(first):
                return first


follow_seen: List[str] = []


def FOLLOW(A: str):
    global follow_seen
    follow = set()
    follow_seen.append(A)

    if A == global_start:  # CASE 1
        follow.add('$')

    for head, prods in global_G_prime.items():
        for prod in prods:
            if A in prod[:-1]:  # CASE 2
                first = FIRST(prod[prod.index(A) + 1])
                follow |= (first - set('^'))  # `^` is empty string, i.e. Epsilon
                if ('^' in first) and (head not in follow_seen):  # CASE 3
                    follow |= FOLLOW(head)
            elif (A in prod[-1]) and (head not in follow_seen):  # CASE 3
                follow |= FOLLOW(head)

    follow_seen.remove(A)
    return follow


def CLOSURE(I: Dict[str, List[List[str]]]) -> Dict[str, List[List[str]]]:
    """
    Used to find the whole state from the first production ONLY

    :param I: A partially filled state of the Finite Automata
    :return: Completely filled state
    """
    global global_G_prime, global_nonterminals
    J = I

    while True:
        item_len: int = len(J)
        for head, prods in J.copy().items():
            for prod in prods:
                if '.' not in prod[:-1]:
                    continue
                symbol_after_dot: str = prod[prod.index('.') + 1]
                if symbol_after_dot not in global_nonterminals:
                    continue
                for G_prod in global_G_prime[symbol_after_dot]:
                    if G_prod == ['^']:
                        if symbol_after_dot not in J.keys():
                            J[symbol_after_dot] = [['.']]
                        elif ['.'] not in J[symbol_after_dot]:
                            J[symbol_after_dot].append(['.'])
                    else:
                        if symbol_after_dot not in J.keys():
                            J[symbol_after_dot] = [['.'] + G_prod]
                        elif ['.'] + G_prod not in J[symbol_after_dot]:
                            J[symbol_after_dot].append(['.'] + G_prod)
        if item_len == len(J):
            return J


def GOTO(I: Dict[str, List[List[str]]], X: str) -> Dict[str, List[List[str]]]:
    """
    On reading `X` from state `I`, we get a new state.

    :param I: state of the Finite Automata
    :param X: variable/terminal which is read from state `I`
    :return:  The new state is returned
    """
    goto = {}
    for head, prods in I.items():
        for prod in prods:
            if '.' not in prod[:-1]:  # This is true if all the Symbols of the production are read
                # print(f'WARNING: Inside GOTO -> head={head}, prod={prod}, X={X}');
                continue
            dot_pos = prod.index('.')
            if prod[dot_pos + 1] != X:  # If the symbol after `.` is not `X`, then skip this production
                continue
            for C_head, C_prods in CLOSURE({head: [
                prod[:dot_pos] + [X, '.'] + prod[dot_pos + 2:]
            ]}).items():  # Swap the position of `.` and `X`, and find the closure
                if C_head not in goto.keys():
                    goto[C_head] = C_prods
                else:
                    for C_prod in C_prods:
                        if C_prod not in goto[C_head]:
                            goto[C_head].append(C_prod)
    return goto


# -----------------------------------------------------------------------------------------

def items1():  # Generate all the state of the Finite Automata
    global global_start, global_symbols

    # Stores all the states of the Finite Automata
    C = [CLOSURE({global_start: [['.'] + [global_start[:-1]]]})]
    while True:
        item_len = len(C)
        for Ith_state in C.copy():
            for X in global_symbols:
                goto_i_x_state = GOTO(Ith_state, X)
                if len(goto_i_x_state) > 0 and (goto_i_x_state not in C):
                    C.append(goto_i_x_state)
        if item_len == len(C):
            return C


def construct_table() -> Dict[int, Dict[str, str]]:
    global global_start, global_G_indexed, global_terminals, global_nonterminals, global_C
    parse_table = {
        r: {
            c: '' for c in global_terminals + ['$'] + global_nonterminals
        } for r in range(len(global_C))
    }

    for i, I in enumerate(global_C):
        for head, prods in I.items():
            for prod in prods:
                if '.' in prod[:-1]:  # CASE 2 a  # Add reduce operations to the Parsing table
                    symbol_after_dot = prod[prod.index('.') + 1]
                    if symbol_after_dot in global_terminals:
                        s = f's{global_C.index(GOTO(I, symbol_after_dot))}'
                        if s not in parse_table[i][symbol_after_dot]:
                            # This IF is done to avoid redundant addition of the same shift operation
                            if 'r' in parse_table[i][symbol_after_dot]:
                                parse_table[i][symbol_after_dot] += '/'
                            parse_table[i][symbol_after_dot] += s
                elif prod[-1] == '.' and head != global_start:
                    # CASE 2 b  # Add reduce operations to the Parsing Table  # Executes if `I` is not the starting state
                    for j, (G_head, G_prod) in enumerate(global_G_indexed):
                        # This loop is used to find the index of the production `head -> prod`
                        if G_head == head and (G_prod == prod[:-1] or (G_prod == ['^'] and prod == ['.'])):
                            for f in FOLLOW(head):
                                if parse_table[i][f] != '':
                                    parse_table[i][f] += '/'
                                parse_table[i][f] += f'r{j}'
                            break
                else:  # CASE 2 c  # Add accept to the Parsing Table
                    parse_table[i]['$'] = 'acc'
        for A in global_nonterminals:  # CASE 3  # Add state number under the columns of Variables/NonTerminals
            j = GOTO(I, A)
            if j in global_C:
                parse_table[i][A] = global_C.index(j)
    return parse_table


def print_info():
    global global_G_prime, global_terminals, global_nonterminals, global_symbols
    max_G_prime = len(max(global_G_prime.keys(), key=len))  # Stores the max length of a Variable/NonTerminal string

    print('Augmented Grammar:')
    i = 0
    for head, prods in global_G_prime.items():
        for prod in prods:
            print(f'    {i:>{len(str(len(global_G_indexed) - 1))}}: {head:>{max_G_prime}} -> {" ".join(prod)}')
            i += 1

    print()
    print(f'{"Terminals:":>15} {", ".join(global_terminals)}')
    print(f'{"NonTerminals:":>15} {", ".join(global_nonterminals)}')
    print(f'{"Symbols:":>15} {", ".join(global_symbols)}')

    print('\nFIRST:')
    for head in global_G_prime.keys():
        print(f'    {head:>{max_G_prime}} = {{ {", ".join(FIRST(head))} }}')

    print('\nFOLLOW:')
    for head in global_G_prime.keys():
        print(f'    {head:>{max_G_prime}} = {{ {", ".join(FOLLOW(head))} }}')

    width = max(len(c) for c in ['ACTION'] + global_symbols) + 2  # It is single column width
    for r in range(len(global_C)):
        max_len = max([len(str(c)) for c in global_parse_table[r].values()])
        if width < (max_len + 2):
            width = max_len + 2

    print('\nParsing Table:')
    print(f'+{"-" * width}+{"-" * ((width + 1) * len(global_terminals + ["$"]) - 1)}+{"-" * ((width + 1) * len(global_nonterminals) - 1)}+')
    print(f'|{"":{width}}|{"ACTION":^{(width + 1) * len(global_terminals + ["$"]) - 1}}|{"GOTO":^{(width + 1) * len(global_nonterminals) - 1}}|')
    print(f'|{"STATE":^{width}}+{("-" * width + "+") * len(global_symbols + ["$"])}')
    print(f'|{"":^{width}}|', end=' ')

    for symbol in global_terminals + ['$'] + global_nonterminals:
        print(f'{symbol:^{width - 1}}|', end=' ')

    print(f'\n+{("-" * width + "+") * (len(global_symbols + ["$"]) + 1)}')

    for r in range(len(global_C)):
        print(f'|{r:^{width}}|', end=' ')
        for c in global_terminals + ['$'] + global_nonterminals:
            print(f'{global_parse_table[r][c]:^{width - 1}}|', end=' ')
        print()

    print(f'+{("-" * width + "+") * (len(global_symbols + ["$"]) + 1)}')


# -----------------------------------------------------------------------------------------

def generate_automaton():
    automaton = Digraph('automaton', node_attr={'shape': 'record'})
    max_G_prime = len(max(global_G_prime.keys(), key=len))

    for i, I in enumerate(global_C):
        I_str = f'<<I>I</I><SUB>{i}</SUB><BR/>'
        for (head, prods) in I.items():
            for prod in prods:
                I_str += f'<I>{head:>{max_G_prime}}</I> &#8594;'
                for symbol in prod:
                    if symbol in global_nonterminals:
                        I_str += f' <I>{symbol}</I>'
                    elif symbol in global_terminals:
                        I_str += f' <B>{symbol}</B>'
                    else:
                        I_str += f' {symbol}'

                I_str += '<BR ALIGN="LEFT"/>'

        automaton.node(f'I{i}', f'{I_str}>')

    for r in range(len(global_C)):
        for c in global_terminals + ['$'] + global_nonterminals:
            if isinstance(global_parse_table[r][c], int):
                automaton.edge(f'I{r}', f'I{global_parse_table[r][c]}', label=f'<<I>{c}</I>>')
            elif 's' in global_parse_table[r][c]:
                i = global_parse_table[r][c][global_parse_table[r][c].index('s') + 1:]
                if '/' in i:
                    i = i[:i.index('/')]
                automaton.edge(f'I{r}', f'I{i}', label=f'<<B>{c}</B>>' if c in global_terminals else c)
            elif global_parse_table[r][c] == 'acc':
                automaton.node('acc', '<<B>accept</B>>', shape='none')
                automaton.edge(f'I{r}', 'acc', label='$')

    automaton.view()


def LR_parser(w: str):
    def print_line():
        print(f'{"".join(["+" + ("-" * (max_len + 2)) for max_len in max_lens.values()])}+')

    buffer = f'{w} $'.split()
    pointer = 0
    a = buffer[pointer]
    stack = ['0']
    symbols = ['']
    histories = {'step': [''], 'stack': ['STACK'] + stack, 'symbols': ['SYMBOLS'] + symbols, 'input': ['INPUT'], 'action': ['ACTION']}

    step = 0
    while True:
        s = int(stack[-1])
        step += 1
        histories['step'].append(f'({step})')
        histories['input'].append(' '.join(buffer[pointer:]))

        if a not in global_parse_table[s].keys():
            histories['action'].append(f'ERROR: unrecognized symbol {a}')
            break
        elif not global_parse_table[s][a]:
            histories['action'].append('ERROR: input cannot be parsed by given grammar')
            break
        elif '/' in global_parse_table[s][a]:
            if global_parse_table[s][a].count('r') > 1:
                histories['action'].append(f'ERROR: reduce-reduce conflict at state {s}, symbol {a}')
            else:
                histories['action'].append(f'ERROR: shift-reduce conflict at state {s}, symbol {a}')
            break
        elif global_parse_table[s][a].startswith('s'):
            histories['action'].append('shift')
            stack.append(global_parse_table[s][a][1:])
            symbols.append(a)
            histories['stack'].append(' '.join(stack))
            histories['symbols'].append(' '.join(symbols))
            pointer += 1
            a = buffer[pointer]
        elif global_parse_table[s][a].startswith('r'):
            head, prod = global_G_indexed[int(global_parse_table[s][a][1:])]
            histories['action'].append(f'reduce by {head} -> {" ".join(prod)}')

            if prod != ['^']:
                stack = stack[:-len(prod)]
                symbols = symbols[:-len(prod)]

            stack.append(str(global_parse_table[int(stack[-1])][head]))
            symbols.append(head)
            histories['stack'].append(' '.join(stack))
            histories['symbols'].append(' '.join(symbols))

        elif global_parse_table[s][a] == 'acc':
            histories['action'].append('accept')
            break

    max_lens = {key: max(len(value) for value in histories[key]) for key in histories.keys()}
    justs = {'step': '>', 'stack': '', 'symbols': '', 'input': '>', 'action': ''}

    print_line()
    print(''.join([f'| {history[0]:^{max_len}} ' for history, max_len in zip(histories.values(), max_lens.values())]) + '|')
    print_line()
    for i, step in enumerate(histories['step'][:-1], 1):
        print(''.join([f'| {history[i]:{just}{max_len}} ' for history, just, max_len in
                       zip(histories.values(), justs.values(), max_lens.values())]) + '|')

    print_line()


# -----------------------------------------------------------------------------------------

if __name__ == '__main__':
    import sys

    file_name = 'grammar.txt'
    if len(sys.argv) == 2:
        file_name = sys.argv[1]
    elif len(sys.argv) != 1:
        print("Usage:")
        print("    python SLRParse.py [FILENAME]")
        print("\nWARNING: Only 1 grammar file as input can be passed")
        exit(1)
    print(f"Grammar file = '{file_name}'")

    # all the variables are list except G_prime  # global_start stores `E'` i.e. `E prime`
    global_G_prime, global_G_indexed, global_start, global_terminals, global_nonterminals, global_symbols = parse_grammar(file_name)

    # Find all the states of the Finite Automata for the grammar
    global_C = items1()

    global_parse_table = construct_table()
    print_info()
    generate_automaton()

    LR_parser(input('\nEnter Input: '))
