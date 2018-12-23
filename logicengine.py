from copy import deepcopy
from IPython import embed
import pdb

class predicate:
    def __init__(self, name, relations): #Create a new instance of a predicate
        self.relations = relations
        self.name = name

    def addrelation(self, args, value): #Add a predicate relation to the predicate
        self.relations[args] = value

    def getval(self, args): #Get the value of a predicate relation
        if args in self.relations:
            return self.relations[args]
        return None

    def compatibleassignment(self, constants, arguments): #Unify ground literal with arguments
        satconstants = list()
        for const, arg in zip(constants, arguments):
            if arg != None and const != arg: #If unification doesn't exist, return nothing
                return None
            elif arg == None:
                satconstants.append(const) #If unification exists, return list of unified constants
        return satconstants

    def getsatassignments(self, args, value):
        satisfyingassignments = list() 
        for assignment in self.relations.items(): #For each valid assignment
            key, val = assignment
            satconstants = None
            if val == value: #Check that value of the assignment matches desired value
                satconstants = self.compatibleassignment(key, args)

            if satconstants != None:
                satisfyingassignments.append(satconstants)
        
        return satisfyingassignments #Return all of the possible unified values that yield true

    def getname(self):
        return self.name
            

class rule:
    def __init__(self, identifier, statements, parameters): #A rule has a list of involved predicates and varaibles / constants
        self.parameters = parameters
        self.identifier = identifier
        self.statements = statements
        
    def addpredicate(self, predicateID, value, variables): #Adding a predicate consists of adding the predicate ID, linking the parameters and giving a 
        self.statements.append((predicateID, value, variables))# true/false value
        for var in variables:
            if var not in self.parameters:
                if var[0].isupper(): #If variable is a constant, set it to a constant in the mapping
                    self.parameters[var] = var
                else: #Otherwise, set it to None in the mapping
                    self.parameters[var] = None
    def getparameters(self):
        return self.parameters

    def getidentifier(self):
        return self.identifier

    def getstatements(self):
        return self.statements


#Keeps track of possible bindings and satisfying bindings for the variables of a rule
class environment:
    def __init__(self, bindings):
        self.validassignments = set()
        firstassignment = tuple(bindings.items())
        self.validassignments.add(firstassignment)

    def getvalidbindings(self):
        return list(self.validassignments)

    def getpotentialassignments(bindings, stmt):
        _, _, stmtargs = stmt
        bindingtable = dict()
        for binding in bindings:
            key, value = binding
            bindingtable[key] = value
        argset = tuple()
        for arg in stmtargs:
            argset += bindingtable[arg]
        return argset


    #Given a binding and a result of a query, combine binding and query result to get future valid bindings
    def cascadebindings(self, queryresult, bindings, stmtargs):
        varyingargs = list() 
        bindingtable = dict()
        for binding in bindings: #Construct a hashmap of args to values
            key, value = binding
            bindingtable[key] = value

        for arg in stmtargs: #Grab keys of arguments that would have returned values
            if bindingtable[arg] == None:
                varyingargs.append(arg)

        newbindings = list()
        for result in queryresult: #For each result, construct a new binding and update it with a valid assignment
            newbinding = deepcopy(bindingtable)
            for key, value in zip(varyingargs, result):
                newbinding[key] = value
            newbindings.append(newbinding.items())
        return newbindings


    def update(self, queryresult, binding, stmtargs):
        if type(queryresult) is bool:
            if not queryresult:
                self.validassignments.remove(binding)
        
        else:
            self.validassignments.remove(binding)
            newbindings = self.cascadebindings(queryresult, binding, stmtargs)
            for newbinding in newbindings:
                self.validassignments.add(tuple(newbinding))
        return

    def hasvalidassignment(self):
        return len(self.validassignments) > 0


class LogicEngine:
    def __init__(self, KB=list(), rules=list()):
        self.KB = KB
        self.rules = rules


    def equivalentpreds(self, sentence, predicate, negation, args):
        bindings = sentence.getparameters()
        statements = sentence.getstatements()
        equivalentstmts = set()
        for i in range(len(statements)):
            stmt = statements[i]
            if predicate == stmt[0] and negation == stmt[1]:
                params = stmt[2]
                unifiable = True
                for param, arg in zip(params, args):
                    if bindings[param] != None and arg != None and bindings[param] != arg:
                        unifiable = False
                if unifiable:
                    equivalentstmts.add(i)

        return equivalentstmts

    def querygroundliterals(self, predicate, value, args):
        for pred in self.KB:
            if pred.getname() == predicate: 
                baseval = pred.getval(args) #See if the predicate is valued for the query
                if baseval != None:
                    if baseval == value: #If so, return True if values are equal, false otherwise
                        return True
                    return False
                if baseval == None: #If not, see if some unification is possible to cause truth
                    return pred.getsatassignments(args, value)
        return list()


    #Determine if the given clause and bindings satisfy a query with unification    
    def satisfiesquery(self, clause, bindings, predicate, value, args):
        predID = clause[0]
        negation = clause[1]
        if predID != predicate or negation != value:
            return False
        parameters = clause[2]
        for param, arg in zip(parameters, args):
            paramVal = bindings[param]
            if arg != None and paramVal != None and arg != paramVal:
                return False
        return True


    #Get clauses from rule-base that can satisfy query
    def getsatclauses(self, predicate, value, args, visited):
        satclauses = dict() #Create a mapping of rules to satisfying clauses
        for sentence in self.rules: #For each rule in rule set
            sentenceID = sentence.getidentifier() #Make sure the rule is unvisited
            if sentenceID not in visited:
                bindings = sentence.getparameters() #Get bindings and clauses
                clauses = sentence.getstatements()
                for i in range(len(clauses)): #For each clauses
                    if self.satisfiesquery(clauses[i], bindings, predicate, value, args): #Check to see if clause is compatible with query
                        if sentenceID not in satclauses:
                            satclauses[sentenceID] = set()
                        satclauses[sentenceID].add(i) #If it does, add it to the set of satisfying clauses

        return satclauses

    #Input, a rule and the predicate and arguments to unify it with 
    #Output, a new, unified rule.
    def unify(self, sentence, clause, args):
        statements = sentence.getstatements()
        oldbindings = sentence.getparameters()
        newbindings = dict()
        clausepred, clauseval, clauseparams = statements[clause]
        for param, arg in zip(clauseparams, args):
            if arg != None:
                newbindings[param] = arg

        for binding in oldbindings.items():
            key, value = binding
            if key not in newbindings:
                newbindings[key] = value
            else:
                if value != None and value != newbindings[key]:
                    raise Exception("Unification error: Clauses not unifiable")

        newrule = rule('volatile', deepcopy(statements), newbindings)
        return newrule
        

    def unifyclause(self, binding, args):
        newargs = tuple()
        bindtable = dict()
        for key,val in list(binding):
            bindtable[key] = val
        for arg in args:
            newargs += tuple([bindtable[arg]])
        return newargs

    #Recursively attempts to query until it arrives a conditional or universal yes
    def query(self, predicate, value, args, visited):
        satassignments = self.querygroundliterals(predicate, value, args) #First query ground literals for assignments
        if type(satassignments) is bool or len(satassignments) > 0:
            return satassignments

        satisfyingclauses = self.getsatclauses(predicate, value, args, visited) #If no ground literals satisfy, look for sat clauses
        for ruleID, clauses in satisfyingclauses.items(): #For each potentially satisfying clause
            for clause in clauses: #For each satisfying clause in the sentence
                newvisited = deepcopy(visited)
                newvisited.add(ruleID)
                unifiedRule = self.unify(self.rules[ruleID], clause, args) #Make a new rule by unifing the clause and sentence with query
                ignoredPredicates = self.equivalentpreds(unifiedRule, predicate, value, args) # Filter out redundant clauses
                unifiedBindings = unifiedRule.getparameters() #Grab unified bindings
                environ = environment(unifiedBindings) #Construct environment from bindings
                unifiedStatements = unifiedRule.getstatements()
                for stmtID in range(len(unifiedStatements)): #For each statment in the rule
                    if stmtID not in ignoredPredicates and environ.hasvalidassignment():
                        stmtpred, stmtval, stmtargs = unifiedStatements[stmtID]
                        potentialBindings = environ.getvalidbindings()
                        for binding in potentialBindings: #For each potential assignment of free variables in rule
                            assignment = self.unifyclause(binding, stmtargs)
                            queryresult = self.query(stmtpred, not stmtval, assignment, newvisited)
                            environ.update(queryresult, binding, stmtargs)

                if environ.hasvalidassignment():
                    return True
                        
        return False

    def isgroundliteral(self, arguments):
        for arg in arguments:
            if not arg[0].isupper():
                return False
        return True

    def addpredicaterelation(self, predname, value, arguments):
        for pred in self.KB:
            if predname == pred.getname():
                pred.addrelation(arguments, value)
                return
        #Otherwise it's a new predicate
        newpred = predicate(predname, dict())
        newpred.addrelation(arguments, value)
        self.KB.append(newpred)
        return

    def extractclause(self, clause):
        predname, arguments = clause.split("(")
        arguments = arguments[:-1]
        arguments = arguments.split(",")
        arguments = tuple(arguments)
        value = "~" not in predname
        if not value:
            predname = predname[1:]
        return predname, value, arguments


    def tell(self, sentence):
        clauses = sentence.split("|")
        if len(clauses) == 1:
            predname, value, arguments = self.extractclause(clauses[0])
            if self.isgroundliteral(arguments):
                self.addpredicaterelation(predname, value, tuple(arguments))
                return
        #Otherwise add the rule
        ruleID = len(self.rules)
        newrule = rule(ruleID, list(), dict())
        for clause in clauses:
            predname, value, arguments = self.extractclause(clause)
            newrule.addpredicate(predname, value, arguments)
        self.rules.append(newrule)
        return

    def ask(self, sentence):
        predicate, value, args = self.extractclause(sentence)
        visited = set()
        return self.query(predicate, value, args, visited)


##TODO Test parsing and ability to read a text file
##TODO Add exhaustive searching at every step
