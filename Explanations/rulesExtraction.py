import re
from itertools import cycle

def AnswerSetFinder(Expression, AnswerSetFile):
    # find literals in the Answer Set totally, partially or not grounded
    # INPUTS: Expression -> partially/totally/non-grounded literal in string format
    #         AnswerSetFile -> the file containing the Answer Set obtaioned from SPARC
    # OUTPUT: list of matched grounded terms retrieved from the Answer Set
    #print(Expression)
    if not re.search('[\>\<\=\!]',Expression):
        Expression = re.sub('\(', '\(', Expression)
        Expression = re.sub('\)', '\)', Expression)
        Expression = re.sub('[A-Z][0-9]?', '[a-z0-9_]+(?:\(.+?\))?', Expression)
        #print(Expression)
        literal = re.findall("(?<!-)"+Expression, AnswerSetFile) 
        #print(literal)
    else:
        literal = [Expression]
    return literal


def AxiomsFinder(Literal, ASPfile, option):
    # retrieve axioms in the ASP program that contains a given Literal in its head or body
    # INPUTS: Literal -> partially/totally/non-grounded literal in string format
    #         ASPfile -> the file containing the ASP program
    #         option  -> 'head' or 'body'. Indicates the part of the axiom looking for 
    # OUTPUT: list of matched rules retrieved from the ASP program
    
    Literal = re.sub('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()', '\s?[A-Z]+\+?[0-9]?', Literal)
    Literal = re.sub('\(', '\(', Literal)
    Literal = re.sub('\)', '\)', Literal)
    if option == 'head':
        axiom = re.findall(".*?"+"(?<!-)"+Literal+"\s?:-.*?\.", ASPfile)
    else:
        axiom = re.findall(".*:-.*"+"(?<!-)"+Literal+".*\.", ASPfile)
    return axiom    


def Grounder(axiom, grounded_literal, option):
    # partially/totally ground literals in an axiom based on the ground of other literals from the same axiom
    # INPUTS: axiom            -> the axiom in string format
    #         grounded_literal -> one grounded term in string format
    #         option           -> 'head' or 'body'. Selects the part of the axiom to retrieve 
    # OUTPUT: list of partially/totally grounded terms
    grounds = re.findall('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()',grounded_literal)
    nonground_finder = re.sub('\(', '\(', grounded_literal)
    nonground_finder = re.sub('\)', '\)', nonground_finder)
    nonground_finder = re.sub('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\\\\\()', '\s?([a-zA-Z0-9_\+]+)(?![a-zA-Z0-9_]*\()', nonground_finder)
    variables = re.findall(nonground_finder, axiom)
    for idx, variable in enumerate(variables[0]):
        axiom = re.sub(variable+'(?![a-zA-Z0-9])', grounds[idx], axiom)
    if option == 'body':
        axiom = re.findall("(?<=:-)(.*?)\.", axiom)
    else:
        axiom = re.findall("(.*)(?=:-)", axiom)
    axiom = re.sub('\s','',axiom[0])
    axiom = [re.sub('\.','',x) for x in re.split(':-|,(?=\s*[a-zA-Z#0-9_]+?[\(\=\<\>\!])',axiom)]# if not x.startswith('#')]
    return axiom

def Grounding(axiom, grounded_literal):
    # INPUTS: axiom            -> the axiom in string format
    #         grounded_literal -> one grounded term in string format
    # OUTPUT: two lists containing variables and correspondents grounds
    grounds = re.findall('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()',grounded_literal)
    nonground_finder = re.sub('\(', '\(', grounded_literal)
    nonground_finder = re.sub('\)', '\)', nonground_finder)
    nonground_finder = re.sub('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\\\\\()', '\s?([a-zA-Z0-9_\+]+)(?![a-zA-Z0-9_]*\()', nonground_finder)
    variables = re.findall(nonground_finder, axiom)
    return list(variables[0]), grounds

def validateBody(groundTerms, rule):
    #test if the body of a rule holds based on the set of grounded terms from the answer set
    # INPUTS: groundTerms -> a simple list (or string) of grounded terms
    #         rule        -> the axiom in string format
    # OUTPUTS: 'True' or 'False', which means that a body holds or not
    if not isinstance(groundTerms, list):
        groundTerms = [groundTerms]

    if len(groundTerms) > 1:
        variables = []
        grounds = []
        for term in groundTerms:
            variable, ground = Grounding(rule, term)
            if re.search('[\=\<\>\!]+', term)!=None:
                variab = re.findall('[A-Z]+[a-z0-9]*', term)
                if all([v in variables for v in variab]):
                    equation = term
                    for v in variab:
                        equation = re.sub(v, grounds[variables.index(v)], equation)
                    if not eval(equation):
                        return False
            else:
              for ind, var in enumerate(variable):
                if var in variables:
                    if ground[ind]!=grounds[variables.index(var)]:
                        return False
                else:
                    variables.append(var)
                    grounds.append(ground[ind]) 
            

    terms = re.split(':-|,(?=\s*[a-z#A-Z0-9\s_]+?[\(\=\<\>\!])',rule)
    terms = [re.sub(' ','\n?',re.sub('\(','\(',re.sub('\)','\)',term))) for term in terms[1:]]
    terms = [re.sub('[A-Z][0-9]?', '[a-z0-9_]+(?:\(.+?\))?', re.sub('\.','',term)) for term in terms if not re.search('not|[\>\<\=\!]',term)]
    #print(terms)
    #print([[re.search(term, groundTerm)!=None for groundTerm in groundTerms] for term in terms])
    return all([any([re.match(term, groundTerm)!=None for groundTerm in groundTerms]) for term in terms if not (re.search('[\>\<\=\!]',term) or term.startswith('not'))])


def planDescription(AnswerSet):
    # retrieves planned actions from an Answer set in chronological order
    actions = AnswerSetFinder('occurs(A,I)', AnswerSet)
    #sorting the actions by time-step
    order = [int(re.findall(',\s?([0-9]+)',x)[0]) for x in actions]
    sorted_actions = [action for _,action in sorted(zip(order,actions))]
    #print('****** Plan description **********')
    #print(sorted_actions)
    return sorted_actions


def whyAction(AnswerSet, ASPprogram, action="", timestep=""):
    sorted_actions = planDescription(AnswerSet)
    action = re.sub("\s","",action)
    action = re.sub("\(","\(",action)
    action = re.sub("\)","\)",action)
    action_query = [act for act in sorted_actions if re.search(action,act)!=None and re.search(',\s?'+timestep,act)!=None][0]
    timestep_query = re.findall(',\s?([0-9]+)', action_query)
    exec_conds = [AxiomsFinder('-'+act, ASPprogram, 'head') for act in sorted_actions[sorted_actions.index(action_query)+1:]] 
    exec_conds = [[Grounder(exe, sorted_actions[sorted_actions.index(action_query)+1:][ind],'body') for exe in exec_cond] for ind, exec_cond in enumerate(exec_conds)]
    exec_conds = [[item for x in exec_cond for item in x] for exec_cond in exec_conds]
    exec_conds_init = [[re.sub(',\s?([0-9]+)', ','+str(timestep_query[0]), x) for x in exec_cond] for exec_cond in exec_conds]
    # select only the conditions actually changed in the next timestep
    exec_conds = [[re.sub(',\s?([0-9]+)', ','+str(int(timestep_query[0])+1), x) for x in exec_cond] for exec_cond in exec_conds]
    exec_conds = [[[AnswerSetFinder(x, AnswerSet), indout + int(timestep_query[0]) + 1] for indin, x in enumerate(exec_cond) if AnswerSetFinder(x, AnswerSet)!=[] and AnswerSetFinder(exec_conds[indout][indin], AnswerSet)==[]] for indout, exec_cond in enumerate(exec_conds_init)]
    exec_conds = [item for cond in exec_conds for item in cond if cond!=[]]
    explanation = max(exec_conds, key=lambda x: x[1])
    explanation = [explanation[0][0], sorted_actions[explanation[1]]]
    print(explanation)
    return explanation


def whyNotAction(AnswerSet, ASPprogram, action, timestep='0'):
    action = re.sub("\s","",action)
    action_query = "occurs("+re.findall('([a-z]+?\([a-zA-z0-9_,]+?\))', action)[0]+","+timestep+")"
    timestep_query = eval(timestep)
    exec_conds = AxiomsFinder('-'+action_query, ASPprogram, 'head')
    exec_conds = [Grounder(exe, action_query,'body') for exe in exec_conds] 
    exec_conds = [item for x in exec_conds for item in x]
    exec_conds = [AnswerSetFinder(x, AnswerSet) for x in exec_conds]
    exec_conds = [item for cond in exec_conds for item in cond if cond!=[] and not item.startswith('#')]
    statics = ['has_surface', 'has_size'] # list of statics
    exec_conds = [exec_cond for exec_cond in exec_conds if 'holds' in exec_cond or 'has_' in exec_cond]
    tower = [exec_cond for exec_cond in exec_conds if 'tower' in exec_cond]
    if tower != []:
        if eval(re.findall('\([a-z_0-9]+?,(\d+?)\)',tower[0])[0]) < 4:
            exec_conds.remove(tower[0]) 
    explanation = [exec_conds]
    print(explanation)
    return explanation


def whyBelief(AnswerSet, ASPprogram, belief, timestep=""):
    axiom = belief
    while axiom!=[]:
        explanation = axiom
        axioms = [[AxiomsFinder(ax, ASPprogram, 'head') for ax in axio][0] for axio in axiom]
        state_constr = [[Grounder(ax, axiom[ind][0],'body') for ax in axi] for ind, axi in enumerate(axioms)]
        state_constr = [item for x in state_constr for item in x]
        state_constr = [[AnswerSetFinder(x, AnswerSet) for x in state_cons] for state_cons in state_constr]
        state_constr = [[x for x in state if not (x==[] and len(state)>1)] for state in state_constr]
        comb = []
        for state in state_constr:
            if len(state)<2:
                comb.append(state)
            if len(state)==2:
                comb.append([[x,y] for x in state[0] for y in state[1]])
            if len(state)==3:
                comb.append([[x,y,z] for x in state[0] for y in state[1] for z in state[2]])
        rules = [item for x in axioms for item in x] #These are the reshaped axioms for being used to body validation
        state_constr = [[st for st in state if validateBody(st, rules[ind])] for ind, state in enumerate(comb)] 
        state_constr = [state[0] for state in state_constr if state!=[]]     
        axiom = [[item] for x in state_constr for item in x]
    print(explanation)
    return explanation

######## OPENNING REQUIRED FILE: Answer Set and ASP program #####
#openning Answer set file
t = open('temp.sp',"r")
ASPprogram = t.read()
t.close()
#openning ASP file
f = open('AnswerSets',"r")
AnswerSet = f.read()
f.close()
#################################################################

#explanation = whyNotAction(AnswerSet, ASPprogram, 'pickup(rob1,red_block)')

#explanation = whyAction(AnswerSet, ASPprogram, timestep="0")

#belief = whyBelief(AnswerSet, ASPprogram, [['-holds(stable(book3),0)']])#,['-holds(stable(book3),0)']])

