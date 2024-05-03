#
# Here we will write code for sat solver
#

import time 
import copy

"""
Input is in CNF DIMACS FORMAT:

p cnf <num_vars> <num_clauses>
<clause1>
<clause2>
...
<clauseN>

Each clause contains disjunctions.
All clauses are connected by conjunctions.

Example: (x1 v x2) & (x2 v x3) & (x2 v x4)

"""

def unit_propagate(literal, clauses):
    simplified_clauses = []

    for c in clauses:
        
        if literal * (-1) in c:
            c_new = copy.deepcopy(c)
            c_new.remove(literal * (-1))
            simplified_clauses.append(c_new)

        elif literal not in c:
            c_new = copy.deepcopy(c)
            simplified_clauses.append(c_new)

    return simplified_clauses

def exists_unit_clause(clauses):
    for el in clauses:
        if len(el) == 1:
            return True
    return False

def return_unit_clause_literal(clauses):
    for el in clauses:
        if len(el) == 1:
            return el[0]
    return 0

def DPLL (clauses, true_variables, literals_to_check):
    """
    Parameters:

    Returns:
    
    """
    if len(clauses) == 0:
        return True
    elif [] in clauses:
        return False
    
    next_clauses = []
    new_true_variables = []
    #
    # Unit propagation

    while exists_unit_clause(clauses):
        literal = return_unit_clause_literal(clauses)
        clauses = unit_propagate(literal, clauses)
        #print(literal)

    #print("clauses1")
    #print(clauses)
    #
    # Pure literal elemination
    
    #while exists_pure_literal(clauses):
        #Heuristics    
    #
    
    l = literals_to_check[0] # pozitivna vrednost int
    literals_to_check.remove(l)

    #case 1 recimo, da l je resničen
    # če je l resničen, so zadovoljivi vsi clausi, ki vsebujejo l
    # clausi z -l so zadovoljivi, če je preostanek clausa zadovoljiv: False v C == True iff C == True 
    next_clauses_case1 = copy.deepcopy(clauses)
    
    #case 2 recimo, da l ni resničen
    # če je -l resničen, so zadovoljivi vsi clausi, ki vsebujejo -l
    # clausi z l so zadovoljivi, če je preostanek clausa zadovoljiv: False v C == True iff C == True 
    next_clauses_case2 = copy.deepcopy(clauses)

    #print("next_clauses")

    #print(next_clauses)
    for c in next_clauses:
        # c vsebuje l
        if l in c:
            # če je l resničen (case 1), takega clausa ne dodajamo v next_clauses_case1 
            #(ker je že cel clause resničen, ne glede na ostale vrednosti)
            
            # če je l neresničen (case 2), je treba pogledati preostanek clausa (tega dodamo v next_clauses_case2)
            
            c_new = copy.deepcopy(c)
            c_new.remove(l)
            next_clauses_case2.remove(c)
            next_clauses_case2.append(c_new)
            

        if (-1) * l in c:
            # če je -l neresničen (case 2), takega clausa ne dodajamo v next_clauses_case1 
            #(ker je že cel clause resničen, ne glede na ostale vrednosti)
            
            # če je -l resničen (case 1), je treba pogledati preostanek clausa (tega dodamo v next_clauses_case2)

            c_new = copy.deepcopy(c)
            c_new.remove((-1) * l)
            next_clauses_case1.remove(c)
            next_clauses_case1.append(c_new)


        if l not in c or (-1) * l not in c:
            c_new = copy.deepcopy(c)
            c_new.remove(l)
            next_clauses_case1.append(c_new)
            next_clauses_case2.append(c_new)
        # c vsebuje -l

        # c ne vsebuje l, dodamo c v oba lista
    #print("hello")
    #print (next_clauses_case1)
    #print (next_clauses_case2)

    return DPLL (next_clauses_case1, true_variables, literals_to_check) or DPLL (next_clauses_case2, true_variables, literals_to_check)

if __name__=="__main__":
    t_start = time.time()

    # Start reading after reaching the first line of dimacs format (p cnf <num_vars> <num_clauses>).
    save_clauses = False
    
    #
    num_vars = 0 
    
    #
    num_clauses = 0

    all_clauses = []

    #with open('input_output/my_example.txt', 'r') as file:
    with open('input_output/sudoku_easy.txt', 'r') as file:

        for line in file:
            symbols = line.strip().split()
            
            if symbols[0] == 'p' and symbols[1] == 'cnf':
                num_vars = int(symbols[2])
                num_clauses = int(symbols[3])
                save_clauses = True

            elif save_clauses:
                integer_list = [int(element) for element in symbols]
                integer_list = integer_list[:-1] # we drop last 0
                #print(integer_list)
                all_clauses.append(integer_list)

    all_clauses= sorted(all_clauses, key=len)
    #print(all_clauses)

    literals_to_check = [i for i in range(1, num_vars + 1)]
    sol = DPLL(all_clauses, [], literals_to_check)
    print(sol)
    t_end = time.time() - t_start
    print(t_end)