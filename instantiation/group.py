from z3 import *
from instlib import *

# We're going to use z3py and some simple instantiation functions from instlib
# The idea is to prove theorems in FOL of the form (quantified premises) => (qfree goal)
# In this case, we're going to use group axioms to show that inverse is unique

# Declare the sort
G = DeclareSort('G')

# Declare your constants and functions
e = Const('e', G)
mul = Function('mul', G, G, G)
inv = Function('inv', G, G)

# Encode premises as pairs of the form (tuple of quantified vars, body)
# You may have to invent some variables for this
x, y, z = Consts('x y z', G)  # Although these are variables, we still declare with Const/Consts
assoc = ((x, y, z),
         mul(x, mul(y, z)) == mul(mul(x, y), z))
identity = ((x,),  # You can denote a singleton tuple by writing (x,)
            And(mul(x, e) == x, mul(e, x) == x))
inverse = ((x,),
           And(mul(x, inv(x)) == e, mul(inv(x), x) == e))

# Write down the list of constants and functions
constants = [e]
functions = [mul, inv]
# Write down the list of axioms as well
premises = [assoc, identity, inverse]

# Express your goal. You may need to invent new variables for this.
a, b = Consts('a b', G)
# If x2 behaves like the left and right inverse, then it is the unique inverse
goal = Implies(And(mul(a, b) == e, mul(a, b) == e),
               b == inv(a))

#### Using instlib to prove your goal correct ###

# Call compute_terms with parameter i to recover terms of height i
# The first 4 arguments are boilerplate. You will not typically find the need to tamper with these
terms = compute_terms(G, constants, functions, goal, height=1)

# Call instantiate with a set/list of premises and a set of terms
# instantiations = instantiate(premises, terms)

# Alternatively, call instantiate with a single premise and a tuple of terms
instantiations = set()
instantiations = instantiations.union(instantiate(inverse, (a,)))
instantiations = instantiations.union(instantiate(assoc, (inv(a), a, b)))
instantiations = instantiations.union(instantiate(identity, (inv(a),)))
instantiations = instantiations.union(instantiate(identity, (b,)))

# Create a z3 solver object and add the negation of the goal as well as your instantiations
s = Solver()
s.add(Not(goal))
s.add(instantiations)
result = s.check()
if result == unsat:
    print('Goal proven')
else:
    print('Goal not proven')
    # When the goal is not proven, you can ask z3 for a model as well
    # This model will help you 'debug' what went wrong with your proof
    m = s.model()
    print(m)
