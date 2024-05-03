#
# Here we will write code for sat solver
#


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

