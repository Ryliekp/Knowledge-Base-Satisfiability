"""
file: satisfiability.py

description: Given a file containing a knowledge base converted to CNF,
             deliteraline if the KB is satisfiable

run command: python3 satisfiability.py filename.cnf

author: Rylie Platt
"""
import sys
from dataclasses import dataclass
from typing import List

# a list of variables used in the KB
VARIABLES = []
# a list of predicates used in the KBf
PREDICATES = []
# a list of constants used in the KB
CONSTANTS = []
# a list of functions used in the KB
FUNCTIONS = []


@dataclass
class Literal:
    """
    Represents a literal in a clause or a function with arguments

    Attributes:
        Predicate (str): The predicate/function name
        Arguments (List[str]): a list of the arguments in the literal/function

    Method:
        substitute: substitutes arguments in the literal/function a new
                    argument after unification
    """
    Predicate: str
    Arguments: List[str]

    def __str__(self) -> str:
        """
        Converts a literal to string format
        :return: a string representation of the literal
        """
        args_string = ", ".join(self.Arguments)
        string = self.Predicate + "(" + args_string + ")"
        return string

    def __hash__(self):
        """
        gets the hash value for the literal
        :return: the hash value for the literal
        """
        return hash((self.Predicate, tuple(self.Arguments)))

    def __eq__(self, other):
        """
        checks if two literals are equal
        :param other: another literal
        :return: True is the literals are equal False if not
        """
        if isinstance(other, Literal):
            predicate = self.Predicate == other.Predicate
            args = self.Arguments == other.Arguments
            return predicate and args
        return False

    def substitute(self, theta):
        """
        Substitutes arguments in theta for a different value
        :param theta: A dictionary containing arguments and their substitutions
        :return: the current literal with its arguments substituted
        """
        new_args = []
        for arg in self.Arguments:
            if arg in theta:
                new_args.append(theta[arg])
            elif isinstance(arg, Literal):
                arg = arg.substitute(theta)
                new_args.append(arg)
            else:
                new_args.append(arg)
        return Literal(self.Predicate, new_args)


def unify(x, y, theta):
    """
    Attempt to unify arguments x and y
    :param x: an arguments from a literal or function
    :param y: an arguments from a literal or function
    :param theta: a dictionary of arguments and their substitutions
    :return: theta, the dictionary of substitutions
    """
    if theta is None:
        return None
    # if x and y are equal
    elif x == y:
        return theta
    # if x or y are variables
    elif x in VARIABLES:
        return unify_var(x, y, theta)
    elif y in VARIABLES:
        return unify_var(y, x, theta)
    # if x or y is a function
    elif isinstance(x, Literal) and isinstance(y, Literal):
        new_theta = unify(x.Predicate, y.Predicate, theta)
        return unify(x.Arguments, y.Arguments, new_theta)
    # if x and y are lists of multiple arguments
    elif isinstance(x, list) and isinstance(y, list):
        return unify(x[0], y[0], unify(x[1:], y[1:], theta))
    # if non-matching constants
    else:
        return None


def unify_var(var, x, theta):
    """
    unify a variable and another argument
    :param var: a variable
    :param x: an arguments from a literal or function
    :param theta: a dictionary of arguments and their substitutions
    :return: theta, the dictionary of substitutions
    """
    # if either are in theta unify with the substitution
    if var in theta:
        val = theta[var]
        return unify(val, x, theta)
    elif x in theta:
        val = theta[x]
        return unify(var, val, theta)
    # if var is in x return false
    elif occur_check(var, x):
        return False
    else:
        # if x is also a variable make a new free variable
        if x in VARIABLES and x != var:
            i = 0
            new = x[0] + str(i)
            while new in VARIABLES:
                new = x[0] + str(i)
                i += 1
            VARIABLES.append(new)
            theta[var] = new
            theta[x] = new
        # add var/x to theta
        else:
            theta[var] = x
        return theta


def occur_check(var, x):
    """
    checks if var is in x
    :param var: a variable
    :param x: an argument
    :return: True if var is in x False if not
    """
    # if x is constant
    if isinstance(x, str):
        return var == x
    # if x is a Function
    elif isinstance(x, Literal):
        if x.Predicate == var:
            return True
        else:
            for arg in x.Arguments:
                if occur_check(var, arg):
                    return True
    # if x is a list of arguments
    elif len(x) > 1:
        for item in x:
            if occur_check(var, item):
                return True
    return False


def make_clause(literal, literal2, clause_one, clause_two):
    """
    make a new literal out of two literals with the cancelled out term missing
    :param literal: a literal in clause_one
    :param literal2: a literal in clause_two
    :param clause_one: a clause containing literal
    :param clause_two: a clause containing literal2
    :return: a new clause made of both clauses without literal or literal two
    """
    new_one = []
    # get all literals from clause_one that aren't literal
    for t in clause_one:
        if t != literal:
            new_one.append(t)
    new_two = []
    # get all literals from clause_two that aren't literal2
    for t in clause_two:
        if t != literal2:
            new_two.append(t)
    # combine both lists of literals
    new_clause = new_one + new_two
    return new_clause


def PL_Resolve(clause_one, clause_two):
    """
    resolve two clauses into new clauses
    :param clause_one: a clause
    :param clause_two: a clause
    :return: a list of clauses created by resolving clause_one and clause_two
    """
    resolvents = set()
    for literal in clause_one:
        if literal.Predicate[0] == "!":
            compliment = literal.Predicate[1:]
        else:
            compliment = "!" + literal.Predicate
        for literal2 in clause_two:
            # only attempt resolving if the literals' predicates are complementary
            # ex: dog and !dog
            if compliment == literal2.Predicate:
                # F.O.L.
                if literal.Arguments and literal2.Arguments:
                    theta = unify(literal.Arguments, literal2.Arguments, {})
                    if theta is not None:
                        new = make_clause(literal, literal2, clause_one, clause_two)
                        copy = []
                        for new_literal in new:
                            new_literal = new_literal.substitute(theta)
                            copy.append(new_literal)
                        resolvents.add(tuple(copy))
                # Prop Logic
                else:
                    new = make_clause(literal, literal2, clause_one, clause_two)
                    resolvents.add(tuple(new))
    return resolvents


def get_pairs(originalClause, compliment, KB):
    """
    get all possible pairs created by matching originalClause
    with other clauses in the database
    :param originalClause: the clause to check for matches of
    :param compliment: the complementary literal we are looking for
    :param KB: the knowledge base
    :return: a list of pairs created by matching originalClause
    with other clauses in the database
    """
    matches = set()
    for clause in KB:
        for literal in clause:
            # match is valid if clause contains compliment
            # and is not originalClause
            if literal.Predicate == compliment and \
                    clause not in matches and \
                    clause != originalClause:
                matches.add(clause)
    return matches


def PL_Resolution(KB):
    """
    Determine if the Knowledge base is satisfiable
    :param KB: the knowledge base
    :return: True if KB is satisfiable False if not
    """
    processed = set()
    while True:
        new = set()
        pairs = []
        for clause in KB:
            matched = set()
            for literal in clause:
                pred = literal.Predicate
                if pred[0] == "!":
                    compliment = pred[1:]
                else:
                    compliment = "!" + pred
                matched = get_pairs(clause, compliment, KB)
            for match in matched:
                pair = [clause, match]
                reverse_pair = [match, clause]
                if tuple(pair) not in processed and tuple(reverse_pair) not in processed:
                    pairs.append([clause, match])
                    processed.add(tuple(pair))
                    processed.add(tuple(reverse_pair))
        for pair in pairs:
            resolvents = PL_Resolve(pair[0], pair[1])
            # if we find {} it is not satisfiable
            if () in resolvents:
                return False
            new = new.union(resolvents)
        # if we cant find a =ny new resolvents it is satisfiable
        if new.issubset(KB):
            return True
        KB = KB.union(new)


if __name__ == '__main__':
    args = sys.argv
    # args = [0, "testcases/functions/f4.cnf"]
    with open(args[1]) as cnf:
        lines = [line.rstrip('\n') for line in cnf]
        PREDICATES = lines[0].split(" ")[1:-1]
        VARIABLES = lines[1].split(" ")[1:]
        CONSTANTS = lines[2].split(" ")[1:]
        FUNCTIONS = lines[3].split(" ")[1:]
        i = 5
        clauses = set()
        while i < len(lines):
            clause = []
            clause_literals = lines[i].rstrip().split(" ")
            for literal in clause_literals:
                if "(" in literal:
                    predicate, args = literal[:-1].split("(", 1)
                else:
                    predicate = literal.strip()
                    args = ""
                args = args.strip().split(",")
                new_args = []
                for arg in args:
                    if "(" in arg:
                        name, func_args = arg[:-1].split("(", 1)
                        func_args = func_args.strip().split(",")
                        newFunc = Literal(name, func_args)
                        arg = newFunc
                        new_args.append(newFunc)
                    else:
                        new_args.append(arg)
                args = new_args
                new_literal = Literal(predicate, args)
                clause.append(new_literal)
            clauses.add(tuple(clause))
            i += 1
        satisfies = PL_Resolution(clauses)
        if satisfies:
            print("yes")
        else:
            print("no")
