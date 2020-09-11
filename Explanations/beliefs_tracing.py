import re
import csv
import random
from anytree import NodeMixin, Node, RenderTree, AsciiStyle, PreOrderIter
import itertools
import os
import operator

ops = {
    '<': operator.lt,
    '<=': operator.le,
    '==': operator.eq,
    '!=': operator.ne,
    '>=': operator.ge,
    '>': operator.gt
    }

class AxiomNode(NodeMixin):
    def __init__(self, name, belief, parent=None, axiom = None):
        super(AxiomNode, self).__init__()
        self.name = name
        self.belief = belief
        self.parent = parent 
        self.axiom = axiom  
    

def axiomFinder(belief, knowledgeInfo):
    # This function returns the literal 'knowledgeInfo' if it is an ungrounded version of belief
    Literal = re.sub('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()','\s?[A-Za-z0-9_+]+[0-9]?', belief.replace(' ',''))
    Literal = re.sub('\(', '\(', Literal)
    Literal = re.sub('\)', '\)', Literal)
    Literal = '(?<!-)'+Literal
    if not re.findall('([a-z][a-z0-9_]+)(?![a-zA-Z0-9_]*\()', knowledgeInfo) or all([re.search('(?<!\w)'+term+'(?!\w)',belief) for term in re.findall('([a-z][a-z0-9_]+)(?![a-zA-Z0-9_]*\()', knowledgeInfo)]):
        return re.findall(Literal, knowledgeInfo)
    
 
def Grounding(axiom, grounded_literal):
    # INPUTS: axiom            -> list containing the predicate to be grounded in position 0 and the nongrounded version of grounded_literal in the position 1
    #         grounded_literal -> one grounded term in string format
    # OUTPUT: the grounded of axiom[0] occording to the grounded_literal
    grounds = re.findall('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()',grounded_literal)
    nonground_finder = re.sub('\(', '\(', grounded_literal.replace(' ',''))
    nonground_finder = re.sub('\)', '\)', nonground_finder)
    nonground_finder = re.sub('([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\\\\\()', '\s?([a-zA-Z0-9_+]+)(?![a-zA-Z0-9_]*\()', nonground_finder)
    variables = re.findall(nonground_finder, axiom[1])
    axiomId = axiom[0]
    for i, term in enumerate(grounds):
        # for dealing with causal laws which effect consolidate in the next time step 'I+1'
        if '+' in variables[0][i]:
           axiomId = re.sub(re.findall('(.+)\+',variables[0][i])[0], str(int(term)-int(re.findall('\+(.+)', variables[0][i])[0])), axiomId)
        else:
            axiomId = re.sub(variables[0][i], term, axiomId)
    return axiomId


def validateBody(groundedBody, answerSet):
    #test if the body of a rule holds based on the answer set
    # INPUTS: groundBody -> a simple list (of strings) of grounded (or semi-grounded) body parts
    #         answerSet        -> Current answer set
    # OUTPUTS: The grounded literals form the answer set that make the body true; if empty the body isn't satisfied
    if all([re.search('[A-Z]+[a-z0-9]*', bodyPart)==None for bodyPart in groundedBody]):
        for ind, bodyPart in enumerate(groundedBody):
            if re.findall('[a-z0-9_]+\n?\=\!?\n?[a-z0-9_]+', bodyPart): 
                r = re.findall('([a-z0-9_]+)\=', bodyPart) == re.findall('\=\!?([a-z0-9_]+)', bodyPart)
                groundedBody[ind] = str(not r) if '!' in bodyPart else str(r)
            if not re.findall('[a-z]', bodyPart):
                if any([not eval(bodyPart) for bodyPart in groundedBody if re.search('[\=\<\>\!]+', bodyPart)!=None]):
                    return []
            else:
                if re.search('[\=\<\>\!]+', bodyPart)!=None:
                    operation = ops.get(re.findall('[\=\<\>\!]+', bodyPart)[0])
                    print re.findall('\w+(?=[\=\!\<\>])', bodyPart)[0]
                    print re.findall('(?<=[\=\!\<\>])\w+', bodyPart)[0]
                    print re.findall('[\=\<\>\!]+', bodyPart)[0]
                    if operation(re.findall('\w+(?=[\=\!\<\>])', bodyPart)[0], re.findall('(?<=[\=\!\<\>])\w+', bodyPart)[0]):
                        return []  
        if any([(bodyPart[3:] in answerSet) for bodyPart in groundedBody if bodyPart.startswith('not')]):
            return []
        if any([(bodyPart not in answerSet) for bodyPart in groundedBody if not (re.search('[\>\<\=\!]',bodyPart) or bodyPart.startswith('not'))]):
            return []
        else: 
            return [groundedBody]           
    else:
        expressions = []
        groundCands = []
        variables = []
        varExpress = []     
        for bodyPart in groundedBody:
            expressions.append(re.sub('[A-Z]+[a-z0-9]*', '\s?[A-Za-z0-9_]+\+?[0-9]?', re.sub('\(','\(', re.sub('\)','\)',bodyPart))))
            groundCands.append([re.findall(expressions[-1], answer)[0] for answer in answerSet if re.findall(expressions[-1], answer)])
            varExpress.append(re.sub('[A-Z]+[a-z0-9]*', '([a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()', re.sub('\(','\(', re.sub('\)','\)',bodyPart))))
            variables.append(re.findall('[A-Z]+[a-z0-9]*', bodyPart))
        variables = [elem for sublist in variables for elem in sublist]
        indVar = [[i for i, var in enumerate(variables) if var == m] for m in variables]
        groundCands = [ground for ground in groundCands if ground]
        if len(groundCands) < 2 and any(groundCands):
            candBodies = groundCands[0]
        else:    
            candBodies = list(itertools.product(*groundCands))
        grounds = []
        for candidate in candBodies:
            terms = [re.findall(express, cand) for express, cand in zip(varExpress, candidate)]
            terms= [elem for sublist in terms for elem in sublist]
            indTerms = [[i for i, term in enumerate(terms) if term == n] for n in terms]
            if indTerms == indVar or len(variables) == len(set(variables)):
                grounds.append(candidate)
        return [grounds]
 
            
            
# This function the axioms from the ASP program to a csv database.
def writer(pathProgram, csvfile):
    programParts = ['sorts', 'predicates', 'rules', 'display']
    with open(pathProgram,"r") as base:
        agent_base_w = [line.strip() for line in base]
        agent_base_w = list([line for line in agent_base_w if line and not line.startswith('%') and not line.startswith(':-')])
    database = []
    count = 0
    multiline = 0    
    for i, line in enumerate(agent_base_w):
        if (not line.endswith('.') or multiline or '%' in line) and (not line in programParts):
            if '.' in line and not multiline:
                spl = line.split('.')
                for sp in spl:
                    if sp.strip().startswith('%'):
                        break
                    else:
                        database.append(sp.strip())
                        count += 1
            else:
                multiline = 1
                if len(database) < count + 1:
                    database.append(line.strip())
                else:
                    database[-1] += line.strip()
                if line.endswith('.'):
                    multiline = 0
                    count += 1
        else:
            database.append(line.strip())
            count+=1
    database = database[database.index('rules')+1:database.index('display')]
    with open(csvfile, 'w') as results:
        wr = csv.writer(results, quoting=csv.QUOTE_ALL)
        for axiom in database:
            wr.writerow(axiom.replace('.','').split(':-'))
    knowledgebase = []
    for axiom in database:            
        knowledgebase.append(axiom.replace('.','').replace(' ','').split(':-'))
        if len(knowledgebase[-1]) < 2:
            knowledgebase[-1].append('')
    return knowledgebase            

##### Writing the axioms from the ASP program to a list

knowledgeBase = writer('ASP_tabletop.sp','database2.csv')

 
# running the ASP program
os.system("java -jar sparc.jar ASP_tabletop.sp -A -solver dlv -solveropts '-n=1'> answer_set")
 
# loading the augmented answer set   
answerSet_file = open('answer_set', 'r')
answerSet = answerSet_file.readlines()[0]
answerSet = answerSet.replace('{','')
answerSet = answerSet.replace('}','')
answerSet = answerSet.replace('\n','')
answerSet = answerSet.split(', ')

# belief to be justified
# random choice to be replaced by the user's choice#####################
beliefs = ['axiom']                                                    # 
while 'axiom' in beliefs[0] or beliefs[0][0]=='#':                     #
    beliefs = [[random.choice(answerSet)]]                             #
beliefs = [['-occurs(pickup(rob1, red_cube_large),0)']]#'holds(relation(above,pitcher,red_cube_large),0)', 'holds(in_hand(rob1,blue_ball),0)', 'holds(in_hand(rob1,red_cube_large), 4)', ]]        #
                                                                       #
########################################################################

beliefsTree = []

nBeliefs = 0 
nCandidate = 0
nParents = 0

beliefsTree.append(AxiomNode('belief0', beliefs[0])) 

stop = 0

while not stop:
    extendedBeliefs = []
    for belief in beliefs: 
      if belief != [()]:
        while isinstance(belief[0], list) or isinstance(belief[0], tuple):
            if len(belief) == 1:
                belief = belief[0]
        nBeliefs += 1 
        
        # list of axioms in the knowledge base that may explain the specific literal in the answer set 
        candidateAxioms = [[line for line in knowledgeBase if axiomFinder(literal,line[0])] for literal in belief] 
        candidateBeliefs = []
        #candidateAxioms = []
        for indCand, candidateSet in enumerate(candidateAxioms):
          if candidateSet:
            candidateBelief = []
            candidateAxiom = []
            for candidate in candidateSet:
                # Check if axiom candidate was used to select any ancestor, it is discaded to avoid a branch in loop
                if any([candidate == n.axiom for n in list(beliefsTree[nBeliefs-1].path)]):
                    continue          
                        
                if candidate[1]:
                    body = re.split(',(?![^(]*\))', candidate[1])
                    # grounding the body parts
                    bodyGround = [Grounding([bod, candidate[0]], belief[indCand]) for bod in body] 
                    # checking body parts ...
                    if validateBody([re.sub('\.','',groundLit) for groundLit in bodyGround], answerSet):
                        groundedBody = validateBody([re.sub('\.','',groundLit) for groundLit in bodyGround], answerSet) 
                        for grounded in groundedBody:
                            if grounded:
                                candidateBelief.append([grounded, candidate]) 
                    
                else:
                    candidateBelief.append([None, candidate])
                    #candidateAxiom.append(candidate)
            
            if candidateBelief:        
                 candidateBeliefs.append(candidateBelief)

        for candidatePair in candidatePairs:
            if all([candidateP[0] == None or not candidateP[1][1] for candidateP in candidatePair]):
                stop = 1
                nCandidate += 1
                candLeaf = [candidate[1] for candidate in candidatePair]
                beliefLeaf = [candidate[0] for candidate in candidatePair if candidate[0]]
                beliefsTree.append(AxiomNode('belief'+str(nCandidate), beliefLeaf, parent = beliefsTree[nParents], axiom = candLeaf))
                    # retreiving the branch containing the explanation
                explanation = [i.name for i in list(beliefsTree[-1].path)] # for the path fram leaf to root
                break
            else:
                nCandidate += 1
                candNode = []
                beliefNode = []
                for candidate in candidatePair: 
                    candNode.append(candidate[1]) 
                    if candidate[0]:
                        beliefNode.append(candidate[0][0])
                beliefsTree.append(AxiomNode('belief'+str(nCandidate), beliefNode, parent = beliefsTree[nParents], axiom = candNode)) 
                extendedBeliefs.append(beliefNode)
        if stop:
            break
    beliefs = extendedBeliefs
 
    if not beliefs:
        stop = 1           
    nParents += 1
    
print (RenderTree(beliefsTree[0], style=AsciiStyle()).by_attr())
 
for beliefs in beliefsTree:  
    print beliefs.name+' : '
    print beliefs.belief 
    print beliefs.axiom


