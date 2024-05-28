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

def max_index(clauses):
    maximum = 0
    for c in clauses:
        for literal in c:
            if literal < 0:
                if -literal > maximum:
                    maximum = -literal
                else:
                    pass
            if literal > maximum:
                maximum = literal
            else:
                pass
    return maximum

def unit_propagate(literal, clauses):
    simplified_clauses = []

    for c in clauses:
        
        if literal * (-1) in c:
            #
            # the negation of a literal occurs in a clause - we simplify the clause by removing the literal negation 
            #
            c_new = copy.deepcopy(c)
            c_new.remove(literal * (-1))
            while (literal * (-1)) in c_new:
                c_new.remove((literal * (-1)))
            
            simplified_clauses.append(c_new)

        elif literal not in c:
            #
            # the literal nor its negation occur in a clause - we keep the whole clause
            #
            c_new = copy.deepcopy(c)
            simplified_clauses.append(c_new)

    return simplified_clauses

def exists_pure_literal(clauses):

    maximum = max_index(clauses)
    positive_literals = maximum * [0]
    negative_literals = maximum * [0]

    for c in clauses:
        for literal in c:
            if literal < 0:
                negative_literals[-literal-1] += 1
            if literal > 0:
                positive_literals[literal - 1] += 1

    max_literal = 0
    for i in range(1, maximum + 1):
        if positive_literals[i - 1] == 0 and negative_literals[i-1] > 0:
            if max_literal < negative_literals[i-1]:
                max_literal = i
        elif negative_literals[i-1] == 0 and positive_literals[i-1] > 0:
            if max_literal < positive_literals[i-1]:
                max_literal = i
        else:
            pass

    return max_literal

def exists_unit_clause(clauses):
    #
    # Return True if there exists a unit clause, otherwise False
    #
    for el in clauses:
        if len(el) == 1:
            return True
    return False

def return_unit_clause_literal(clauses):
    #
    # returns a unit class literall if it exists, otherwise returns 0
    #
    for el in clauses:
        if len(el) == 1:
            return el[0]
    return 0

global DPLL_final_result 
DPLL_final_result = []

def DPLL (clauses, true_variables):
    """
    Recursive function that implements DPLL algorithm for solving SAT expression.

    Parameters:
    clauses (list of lists) - It corresponds to list of all SAT clauses that need to be investigated. 
        Each clause is represented as a list of literals (positive or negative integer values).
    true_variables (list of Int) - It corresponds to a list that tells us which literals were assumed to be true
        at the beginning of the current iteration (based on previous recursive calls this list grows iteratively).

    Returns:
        True: if SAT expression represened by clauses is satisfiable. A concrete solution is saved
          to global "DPLL_final_result" variable (if a literal is not listed there, it is assumed 
          it can be either True or False).
        False: if SAT expression is not satisfiable.
    
    """
    #
    #   Step 0: Check the stopping condition.
    #
    global DPLL_final_result 
    if len(clauses) == 0:
        
        DPLL_final_result = true_variables
        return True
    
    elif [] in clauses:
        return False
    
    next_clauses = clauses
    new_true_variables = true_variables
    
    #
    # Step 1: Unit propagation.
    #
    while exists_unit_clause(next_clauses):
        # return a unit clause literal
        literal = return_unit_clause_literal(next_clauses)
        # simplify clauses and keep only those that do not include literal or they contain literal negation  
        next_clauses = unit_propagate(literal, next_clauses)
        #print("in while")
        if literal not in new_true_variables:
            new_true_variables.append(literal)

    #
    #   Step 1B: Check the stopping condition again.
    #
    if len(next_clauses) == 0:
        DPLL_final_result = new_true_variables
        return True
    elif [] in next_clauses:
        return False
    
    #
    # Step 3: Pure literal elemination and selecting the next literal.
    #
    l = next_clauses[0][0]
    pure_literal_res = exists_pure_literal(next_clauses) 
    if  pure_literal_res > 0:
        l = pure_literal_res

    #Case 1: assume that l is True
    #   if l is True - all clauses containing l are True 
    #   clauses containing -l are satisfiable if the rest is satisfiable: False v C == True iff C == True 
    next_clauses_case1 = []
    true_variables_case1 = copy.deepcopy(new_true_variables)
    true_variables_case1.append(l) # We assume that l is True.
    
    #Case 2: assume that l is False:
    #   if -l is True all clauses containing -l are True
    #   clauses containing l are satisfiable if the rest is satisfiable: False v C == True iff C == True 
    next_clauses_case2 = []
    true_variables_case2 = copy.deepcopy(new_true_variables)
    true_variables_case2.append((-1 * l)) # We assume that -l is True.
    
    for c in next_clauses:

        if l in c and (-1) * l not in c:
            # - if l is True (case 1), the whole clause is True - we don't add such clause
            # to next_clauses_case1, since it is already satisfied. 
            
            # - if l is False <=> -l is True (case 2), we need to take a look at the rest of the clause - we remove l from clause 
            # and add the rest of the clause to next_clauses_case2.
            
            c_new = copy.deepcopy(c)
            # remove all occurences of l
            while l in c_new:
                c_new.remove(l)
            next_clauses_case2.append(c_new)
            

        if (-1) * l in c and l not in c:
            # - if -l is False <=> l is True (case 2) we don't add such clause to next_clauses_case1 
            # (because it is already satisfied)
            # - if -l is True <=> l is False (case 1) we need o take a lookt at the rest of the clause -
            # the rest of the clause is added to (next_clauses_case2)

            c_new = copy.deepcopy(c)
            
            # remove all occurences of l
            while ((-1) * l) in c_new:
                c_new.remove(((-1) * l))
            next_clauses_case1.append(c_new)

        if l not in c and (-1) * l not in c:
            #
            # - if neither l nor -l are present in a clause, we need to take a look at the whole clause 
            # in both cases.
            #

            c_new = copy.deepcopy(c)
            next_clauses_case1.append(c_new)
            next_clauses_case2.append(c_new)

    #
    # Check if SAT expression is satisfiable in any of the 2 cases (if the chosen literal is True and if it is False)
    #
    return DPLL (next_clauses_case1, true_variables_case1) or DPLL (next_clauses_case2, true_variables_case2)


def is_satisfying_solution(cnf, solution):
    """
    Check if the given solution satisfies the CNF expression.

    :param cnf: List of lists, where each sublist represents a clause in CNF form.
    :param solution: List of integers representing the suggested solution.
    :return: True if the solution satisfies the CNF expression, False otherwise.
    """
    # Convert solution to a dictionary for quick lookup
    solution_dict = {abs(lit): lit > 0 for lit in solution}

    # Check each clause in the CNF
    for clause in cnf:
        clause_satisfied = False
        for literal in clause:
            var = abs(literal)
            if var in solution_dict:
                # Check if the literal's value matches the solution's value
                if solution_dict[var] == (literal > 0):
                    clause_satisfied = True
                    break
            else:
                # If the variable is not in the solution, it can be either true or false
                clause_satisfied = True
                break
        
        # If any clause is not satisfied, the whole CNF is not satisfied
        if not clause_satisfied:
            print("Clause not satisfied")
            print(clause)
            return False

    return True



if __name__=="__main__":
    t_start = time.time()

    # Start reading after reaching the first line of dimacs format (p cnf <num_vars> <num_clauses>).
    save_clauses = False
    
    num_vars = 0 
    num_clauses = 0

    all_clauses = []

    file_name = 'input_output/sudoku_easy.txt'
    file_name2 = 'input_output/sudoku_easy_solution.txt'
    
    file_name = "input_output/additional_examples/inputQ25.txt"
    file_name2 = "input_output/additional_examples/outputQ25.txt"
    
    with open(file_name, 'r') as file:

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

    sol = DPLL(all_clauses, [])

    print("solution:")
    print(sorted(DPLL_final_result))
    symbols = []

    if sol:
        with open(file_name2, 'r') as file:
            line = file.readline()
            symbols = list(map(int, line.split()))
            symbols = sorted(symbols)
            sorted_solution = sorted(DPLL_final_result)
            """
            for i in range (0, len(symbols)):
                if symbols [i] == sorted_solution[i]:
                    pass
                else:
                    print('narobe', symbols[i]," ", sorted_solution[i])
            """
            print('deluje')
    else:
        with open(file_name2, 'r') as file:
            line = file.readline()
            
        print("ni resitve ", line)
    
    result = is_satisfying_solution(all_clauses, DPLL_final_result)
    print("Does the solution satisfy the CNF expression?", result)

    result = is_satisfying_solution(all_clauses, symbols)
    print("Does the 2nd solution satisfy the CNF expression?", result)


    t_end = time.time() - t_start
    print(t_end)