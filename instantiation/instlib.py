import itertools
import z3


# Function to compute terms of height i for the POPL 18 fragment
def compute_terms(sort, consts, funcs, formula, height):
    assert all(c.sort() == sort for c in consts), \
        "Constants must be the same sort as the 'sort' argument"
    assert all(all(f.domain(j) == sort for j in range(f.arity())) for f in funcs), \
        "Function can only take arguments from the sort in the 'sort' argument"

    # Collect constants of the sort from the given formula
    new_consts = compute_consts(sort, formula)
    consts = consts + new_consts

    # Compute terms of desired height from the constants and the function symbols
    terms = []
    height_minusone_terms = list(set(consts))
    funcs = list(set(funcs))
    for ctr in range(1, height+1):
        new_height_minusone_terms = []
        for f in funcs:
            arity = f.arity()
            argslist = itertools.product(height_minusone_terms, repeat=arity)
            new_height_minusone_terms += list(f(*args) for args in argslist)
        terms = terms + height_minusone_terms
        height_minusone_terms = new_height_minusone_terms
    terms = terms + height_minusone_terms
    # Return the computed terms
    return set(terms)


# Helper function for compute_terms
def compute_consts(sort, expr):
    is_atom = expr.num_args() == 0
    if is_atom:
        if expr.sort() == sort:
            return [expr]
        else:
            return []
    else:
        constlist = []
        for subexpr in expr.children():
            constlist = constlist + compute_consts(sort, subexpr)
        return constlist


# Helper method for instantiation
def instantiate_aux(qvars, argtuple, body):
    pairs = tuple((qvars[i], argtuple[i]) for i in range(len(qvars)))
    return z3.substitute(body, *pairs)


# Instantiation function
def instantiate(paired_exprs, args):
    formulas = set()
    if type(paired_exprs) == tuple:
        assert len(paired_exprs) == 2, "Premises should be a pair of the form (quantified_vars, body)"
        qvars, body = paired_exprs
        if type(args) != tuple:
            assert type(args) == set, "Arguments to instantiate should either be a tuple or a set"
            argslist = list(itertools.product(args, repeat=len(qvars)))
        else:
            argslist = [args]
        for argtuple in argslist:
            formulas.add(instantiate_aux(qvars, argtuple, body))
        return formulas
    else:
        assert type(args) == set, \
            "Arguments to instantiate can only be a set when trying " \
            "to instantiate multiple formulas at once"
        for qvars, body in paired_exprs:
            argslist = list(itertools.product(args, repeat=len(qvars)))
            for argtuple in argslist:
                formulas.add(instantiate_aux(qvars, argtuple, body))
        return formulas


# Detect recursive definition applications (as in Mural et al., OOPSLA 2023)
def compute_applications(recdef_symbols, formula):
    appl_dict = {symb: [] for symb in recdef_symbols}
    compute_applications_aux(appl_dict, formula)
    return appl_dict


# Helper method for detecting recdef applications
def compute_applications_aux(appl_dict, expr):
    is_atom = expr.num_args() == 0
    if is_atom:
        return
    else:
        decl = expr.decl()
        if decl in appl_dict:
            appl_dict[decl] += [tuple(expr.children())]
        for subexpr in expr.children():
            compute_applications_aux(appl_dict, subexpr)
        return
