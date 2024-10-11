from z3 import *
from instlib import *

# We're going to use z3py and some simple instantiation functions from instlib
# The idea is to prove theorems in FOL of the form (quantified premises) => (qfree goal)
# In this case, we're going to use group axioms to show that inverse is unique

# This is how you declare an algebraic datatype
List = Datatype('List')
List.declare('nil')
List.declare('cons', ('head', IntSort()), ('tail', List))
List = List.create()

# use variables so you don't have to  say List dot field each time
cons = List.cons
nil = List.nil
is_cons = List.is_cons
is_nil = List.is_nil
head = List.head
tail = List.tail

# Declare your recursively defined symbols
sortedls = Function('sortedls', List, BoolSort())
insertls = Function('insertls', List, IntSort(), List)

# Encode definitions as pairs of the form (tuple of quantified vars, body)
# You may have to invent some variables for this
x = Const('x', List)
k = Const('k', IntSort())
sorteddef = ((x,),
             sortedls(x) == (If(x == nil, BoolVal(True),
                                If(tail(x) == nil, BoolVal(True),
                                   And(head(x) <= head(tail(x)), sortedls(tail(x)))
                                   )))
             )

insertdef = ((x, k),
             insertls(x, k) == (If(x == nil, cons(k, nil),
                                   If(head(x) >= k, cons(k, x),
                                      cons(head(x), insertls(tail(x), k))
                                      )))
             )

# Write down the map of recursively defined functions to their definitions
recdefs_map = {sortedls: sorteddef, insertls: insertdef}

# Express your goal. You may need to invent new variables for this.
n = Const('n', IntSort())
# Inserting any key into a nil list makes it sorted
goal1 = sortedls(insertls(nil, n))


#### Using instlib to prove your properties ###
# Call compute_applications on your formula
# This recovers terms of the form recdef(t) occurring in the formula
# Then use the instantiate method to instantiate the corresponding definition
# Let's abstract this into a function since we're going to use this several times
def unfold_once(rd_map, goal_formula):
    applications_dict = compute_applications(list(rd_map.keys()), goal_formula)
    instantiations = set()
    for recdef, argslist in applications_dict.items():
        for args in argslist:
            instantiations = instantiations.union(instantiate(recdefs_map[recdef], args))
    return instantiations


# Create a z3 solver object and add the negation of the goal as well as your instantiations
s = Solver()
s.add(Not(goal1))
s.add(unfold_once(recdefs_map, goal1))
result = s.check()
if result == unsat:
    print('Goal1 proven')
else:
    print('Goal1 not proven')
    # When the goal is not proven, you can ask z3 for a model as well
    # This model will help you 'debug' what went wrong with your proof
    m = s.model()
    print(m)

# Another example, this time assuming the contract on a smaller list
l = Const('l', List)
# We're defining the goal formula as a function so we can get various versions of it
thm = lambda lst, val: Implies(sortedls(lst), sortedls(insertls(lst, val)))
goal2 = thm(l, k)
# Try to prove the goal as you did above
s = Solver()
s.add(Not(goal2))
s.add(unfold_once(recdefs_map, goal2))
result = s.check()
if result == unsat:
    print('Goal2 proven--- needs assumption of contract')
else:
    print('Goal2 not proven')

# This theorem can only be proved by assuming it for a smaller list
goal3 = Implies(Implies(l != nil, thm(tail(l), k)), thm(l, k))
s = Solver()
s.add(Not(goal3))
s.add(unfold_once(recdefs_map, goal3))
result = s.check()
if result == unsat:
    print('Goal3 proven by assuming contract on smaller ADT!')
else:
    print('Goal3 not proven')


# Finally, an example where you use a lemma.
# Lemmas themselves need proving, which we can do as above.
# We'll see an example where the property we just proved can be used as a lemma.
# New recursively defined symbol
sort_while_append = Function('swa', List, List, List)
# Sort while append uses the above insert method to add a list of new elements into a sorted list
y = Const('y', List)
swadef = ((x, y),
          sort_while_append(x, y) == (If(y == nil, x,
                                         sort_while_append(insertls(x, head(y)), tail(y))
                                         ))
          )
# Update map of recursive definitions-- This is important to do!
recdefs_map = {sortedls: sorteddef, insertls: insertdef, sort_while_append: swadef}

# Property: If x is sorted, then adding y using sort_while_append will produce a sorted list
thm = lambda lst1, lst2: Implies(sortedls(lst1), sortedls(sort_while_append(lst1, lst2)))
# We need to assume the contract on a smaller list (in the second argument) as we did above
goal4 = Implies(Implies(y != nil, thm(insertls(x, head(y)), tail(y))), thm(x, y))
# To prove this goal we will need our previously proved property as a lemma
lemma = ((x, k),
         Implies(sortedls(x), sortedls(insertls(x, k))))
# Let us add instantiations as before, but this time we will also instantiate the lemma
s = Solver()
s.add(Not(goal4))
s.add(unfold_once(recdefs_map, goal4))
# Adding an instance of the lemma
# Commenting out the line below will result in the lemma not being proven
s.add(instantiate(lemma, (x, head(y))))
result = s.check()
if result == unsat:
    print('Goal4 proven using assumption of contract and a lemma!')
else:
    print('Goal4 not proven')
