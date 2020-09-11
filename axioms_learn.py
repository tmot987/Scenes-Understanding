from __future__ import division
import os
import time
import re
import random
import csv
import numpy as np
import string
import collections
from shutil import copyfile
# for tree induction...
import pandas as pd
import math
import itertools
#from random import *
from sklearn import tree
from sklearn.tree import DecisionTreeClassifier
from sklearn.model_selection import train_test_split
import sys
from os import listdir
from os.path import isfile, join
from collections import Counter

# This function combines elements of the pool "places" and of "objects" to create a initial state and an action for simulations. 

def randomState_Action(action, objects, places):
    actionGround = 'none'
    if action == 'pickup':
        actionGround = 'occurs(pickup(rob1,'+random.choice(objects)+'),0).'
        inhd = 0.2
    else:
        obj = 'home'
        place = 'home'
        inhd = 0.7
        while (obj == place):
            obj = random.choice(objects)
            place = random.choice(places)            
        actionGround = 'occurs(putdown(rob1,'+obj+','+place+'),0).'
        
    initialState = []       
    inhand = np.random.choice([1,0], p=[inhd, 1-inhd])
    if inhand:
        objInhand = random.choice(objects)
        initialState.append('holds(in_hand(rob1,'+objInhand+'),0).')
        objects.remove(objInhand)
        if objInhand in places:
            places.remove(objInhand)
   
    while objects:
        ob = random.choice(objects)
        plac = random.choice([i for i in places if i != ob])
        objects.remove(ob)
        if ob in places:
            places.remove(ob)
        if plac != 'table':
            places.remove(plac)
        initialState.append('holds(relation(on,'+ob+','+plac+'),0).') 
    print actionGround
    return initialState, actionGround



# This function writes learned axioms to a file.
def writer(path, source):

    with open(path,"r") as base:
        agent_base_w = [line for line in base]
        
    with open(source,"r") as learning:
        learned_axioms = [line for line in learning]

    agent_edited_with = open('temp.sp','w')
    for i, line in enumerate(agent_base_w):
        agent_edited_with.write(line)
        # write the initial state and the action in the ASP program
        if i == [n+2 for n, ax in enumerate(agent_base_w) if '%% Learned Rules' in agent_base_w[n]][0]:
            for axiom in learned_axioms:
                agent_edited_with.write(axiom)       
    agent_edited_with.close()
    copyfile('temp.sp', path)


# This function run an ASP program, including the action and initial configuration, and save the answer sets to a file.
def planner(path, action, initialState, answerfile):

    with open(path,"r") as base:
        agent_base_w = [line for line in base]

    agent_edited_with = open('temp_with.sp','w')
    for i, line in enumerate(agent_base_w):
        agent_edited_with.write(line)
        # write the initial state and the action in the ASP program
        if i == [n+2 for n, ax in enumerate(agent_base_w) if '%%Initial State:' in agent_base_w[n]][0]:
            for state in initialState:
                agent_edited_with.write(state)       
            agent_edited_with.write(action)
    agent_edited_with.close()
    #running the program and saving the answer set
    start = time.time()
    os.system("java -jar sparc.jar temp_with.sp -A -solver dlv -solveropts '-n=1'> " + answerfile)
    end = time.time()
    planTime = end - start # calculating planning time 

    return planTime



# find literals in the Answer Set totally, partially or not grounded
# INPUTS: Expression -> partially/totally/non-grounded literal in string format
#         AnswerSetFile -> the file containing the Answer Set obtaioned from SPARC
# OUTPUT: list of matched grounded terms retrieved from the Answer Set
def AnswerSetFinder(Expression, AnswerSetFile):
    #openning Answer set file
    f = open(AnswerSetFile,"r")
    AnswerSet = f.read()
    f.close()
    if not re.search('[\>\<\=\!]',Expression):
        Expression = re.sub('\(', '\(', Expression)
        Expression = re.sub('\)', '\)', Expression)
        Expression = re.sub('[A-Z][0-9]?', '\S+(?:\(\S+?\))?', Expression)#'[a-z0-9_]+(?:\(.+?\))?', Expression)
        literal = re.findall("(?<!-)"+Expression, AnswerSet) 
    else:
        literal = [Expression]
    return literal
    
# This function compares two answer sets and output the differences
def compareAnsSet(AnswerSetExp, AnswerSetObs):
    # retrieves Expectation and observation from an Answer set
    expectation = AnswerSetFinder('holds(F,1)', AnswerSetExp)
    observation = AnswerSetFinder('holds(F,1)', AnswerSetObs)
    # comparing Expectation X Observation
    unexpected = [i for i in observation if i not in expectation]
    extra = [j for j in expectation if j not in observation]
    for ext in extra:
        inertialExtra = re.sub(',\s?1', ',0', ext)
        if (inertialExtra in AnswerSetFinder('holds(F,0)', AnswerSetExp)) and (os.lstat(AnswerSetObs).st_size > 5):
            print 'negate'
            print ext
            unexpected.append('-'+ext)
            extra.remove(ext)
    return unexpected, extra
  
  
  
  
# Replacing ground terms for convenient variables   
def relRepresentation(grndLiterals):
    #### "groundLiterals" is a list containing multiple lists in the format [inconsistence, action, relevantFluents, Label] with grounded terms
  AllRelevantFacts = []
  ungroundedLiterals = []
  for groundedLiterals in grndLiterals:  
    #print groundedLiterals
    flat_grndLit = [i for j in groundedLiterals[:-1] for i in j]  
    AllTerms = []
    AllVar = []
    for grndLit in flat_grndLit:
        terms = [term for term in re.findall('([a-z][a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()', grndLit) if term not in Relations]
        var = [None]*len(terms)
        expression = grndLit
        expression = re.sub('\(', '\(', expression)
        expression = re.sub('\)', '\)', expression)
      # 1. Checking if a given term was replaced by a variable already 
        for i, term in enumerate(terms):
            if term in AllTerms:
                var[i] = AllVar[AllTerms.index(term)]
                expression = re.sub(term, var[i], expression)
            else:
                expression = re.sub(term, '[A-Z][0-9]?', expression)
                expression = re.sub(',\s?[0-9]', ',[0-9]', expression)
      #2. Check for the same fluents/actions in the "AllRelevantFacts" and link terms found with the correspondent variable, replacing the "terms" by convenient regular expression.
        if any([re.search(expression, relevantFact) for relevantFact in AllRelevantFacts]):
            var = [re.findall('[A-HJ-Z][0-9]?', relevantFact) for relevantFact in AllRelevantFacts if re.search(expression, relevantFact)][0]
      # 3. for terms not matching any existing variable in the "AllRelevantFacts" in #1, replace terms by variables by looking at sorts.  
        else: 
            for j, term in enumerate(terms):
                if term not in AllTerms:
                    var[j] = [sort[0] for sort in Sorts if term in sort[1]][0]
                    seq = [r[0] for r in [re.findall('(?<='+var[j]+')[0-9]', variable) for variable in list(set(AllVar) | set(var)) if variable] if r]
                    if seq:
                        nTerm = max([int(num) for num in seq]) + 1
                    else:
                        nTerm = 1
                    var[j] = var[j] + str(nTerm)

        AllTerms.extend(terms)
        AllVar.extend(var)
            
      # 4. replace the grounded fluents/action in the "groundLiterals" vector by their ungrounded versions
    ungroundLiteral = []
    for n, literals in enumerate(groundedLiterals[:-1]):
        ungroundedLit = []
        for literal in literals:
            ungrdLit = literal
            for i, term in enumerate(AllTerms):
                ungrdLit = re.sub(term, AllVar[i], ungrdLit)
            ungroundedLit.append(ungrdLit)
        ungroundLiteral.append(ungroundedLit)
     # 5. include the ungrounded flutes/actions in the "AllRelevantFacts" list if not there yet.
        if n == 2:
            AllRelevantFacts = list(set(AllRelevantFacts) | set (ungroundedLit))
    ungroundLiteral.append(groundedLiterals[-1])                
    ungroundedLiterals.append(ungroundLiteral)
                    
  return ungroundedLiterals, AllRelevantFacts
    
    
    
    
# Retrieving the relevant information related to an action and store the terms involved
def relevantInfo(action, answerSetFile, relations, relevantTerms):
    #openning Answer set file
    f = open(answerSetFile,"r")
    answerSet = f.read()
    f.close()
    # identifying the grounded terms in the action
    actionTerms = re.findall('([a-z][a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()', action)
    relevantTerms.extend([i for i in actionTerms if i not in relevantTerms])
    # retrieving all the fluents and constants that contains the relevant terms as argument
    relevantFacts = []
    for term in actionTerms:
        relevantFact = re.findall("(?:\{|\s)(\S*"+term+"\S+\),0\))", answerSet)
        for fact in relevantFact:
            terms = [t for t in re.findall('([a-z][a-zA-Z0-9_]+)(?![a-zA-Z0-9_]*\()', fact) if t not in relations]
            relevantTerms.extend([i for i in terms if i not in relevantTerms]) 
        relevantFacts = list(set(relevantFacts) | set(relevantFact)) # union of 2 lists without repetition

    return relevantFacts, relevantTerms


##########  TREE INDCUTION RELATED FUNCTIONS ############################################################

# FILTERING CANDIDATES

def filter_cands(X_test, candidates, tests, labels, thresholds, level):
    occurrence = [0]*len(candidates)
    negative_count = [0]*len(candidates)
    candidates = [list(i) for i in candidates]
    
    print len(X_test)
    print candidates
    print tests
    print labels
    
    for sample_id in range(len(X_test)):
        # updating candidates information counts
        for idx,cnd in enumerate(candidates):
            if [X_test.iloc[sample_id][feature_names[feature[k]]] for k in cnd] == tests[idx]:
                if labels[idx] == X_label.iloc[sample_id]:
                    occurrence[idx] += 1
                else:
                    negative_count[idx] +=1

    extra_cands = []
    extra_tests = []
    extra_thresholds = []
    extra_labels = []
    #ranking and removing candidades
    idx_del =[]
    for idx,cand in enumerate(candidates):
        if occurrence[idx]/(occurrence[idx] + negative_count[idx] + 0.0001) < level:
            idx_del.append(idx)
        # comparing and deleting similar nodes in the same candidate, e.g., x>2 and x>3 results in the more specific x>3 
        if len(cand) > 1:
            cand_del = []
            for a, b in itertools.combinations(cand, 2):
                if feature[a] == feature[b]:
                    if (tests[idx][cand.index(a)] > thresholds[idx][cand.index(a)]) and (tests[idx][cand.index(b)] > thresholds[idx][cand.index(b)]):
                        if thresholds[idx][cand.index(a)] > thresholds[idx][cand.index(b)]:
                            cand_del.append(cand.index(b))
                        else:
                            cand_del.append(cand.index(a))
                    if (tests[idx][cand.index(a)] < thresholds[idx][cand.index(a)]) and (tests[idx][cand.index(b)] < thresholds[idx][cand.index(b)]):
                        if thresholds[idx][cand.index(a)] > thresholds[idx][cand.index(b)]:
                            cand_del.append(cand.index(a))
                        else:
                            cand_del.append(cand.index(b))
            candidates[idx] = [cand[i] for i in range(len(cand)) if i not in cand_del]
            tests[idx] = [tests[idx][i] for i in range(len(cand)) if i not in cand_del]
            thresholds[idx] = [thresholds[idx][i] for i in range(len(cand)) if i not in cand_del]
    #removing candidates that elaborates higher ranked
    for idx,cand in enumerate(candidates):
        for idx2,cand2 in enumerate(candidates):
            if (idx != idx2):
                if (idx not in idx_del) and (idx2 not in idx_del):
                    # deleting candidates that only elaborates higher ranked candidates
                    if all([feature[w] in [feature[f] for f in cand] for w in cand2]) and (occurrence[idx] <= occurrence[idx2]) and (labels[idx] == labels[idx2]):    
                        if ([thresholds[idx][[feature[h] for h in cand].index(feature[t])] for t in cand2] == thresholds[idx2]):
                            if ([tests[idx][[feature[h] for h in cand].index(feature[t])] for t in cand2] == tests[idx2]):
                                idx_del.append(idx)
                        else:
                            for idc,item in enumerate(cand2):
                                if (tests[idx][[feature[e] for e in cand].index(feature[item])] > thresholds[idx][[feature[e] for e in cand].index(feature[item])]) and (tests[idx2][idc] > thresholds[idx2][idc]):
                                    if (thresholds[idx][[feature[e] for e in cand].index(feature[item])]) > thresholds[idx2][idc]:                                 
                                        candidates[idx2][idc] = candidates[idx][[feature[e] for e in cand].index(feature[item])]
                                        thresholds[idx2][idc] = thresholds[idx][[feature[e] for e in cand].index(feature[item])]
                                        tests[idx2][idc] = tests[idx][[feature[e] for e in cand].index(feature[item])]
                                if (tests[idx][[feature[e] for e in cand].index(feature[item])] < thresholds[idx][[feature[e] for e in cand].index(feature[item])]) and (tests[idx2][idc] < thresholds[idx2][idc]):
                                    if (thresholds[idx][[feature[e] for e in cand].index(feature[item])]) < thresholds[idx2][idc]: 
                                        candidates[idx2][idc] = candidates[idx][[feature[e] for e in cand].index(feature[item])]
                                        thresholds[idx2][idc] = thresholds[idx][[feature[e] for e in cand].index(feature[item])]
                                        tests[idx2][idc] = tests[idx][[feature[e] for e in cand].index(feature[item])]
                            idx_del.append(idx)           

                    # creating possibly more general candidates from other two more elaborated
                    if any([item in cand for item in cand2]) and (labels[idx] == labels[idx2]):
                        if any([tests[idx][cand.index(t)]==tests[idx2][cand2.index(t)] for t in set(cand).intersection(cand2)]):
                            new_cand = []
                            new_test = []
                            new_thresh = []
                            for elem in [item for item in cand if item in cand2]:
                                if tests[idx][cand.index(elem)]==tests[idx2][cand2.index(elem)]:
                                    new_cand.append(elem)
                                    new_test.append(tests[idx][cand.index(elem)])
                                    new_thresh.append(thresholds[idx][cand.index(elem)])
                            if not(new_cand == cand or new_cand == cand2 or new_cand in extra_cands):
                                extra_cands.append(new_cand)
                                extra_tests.append(new_test)
                                extra_thresholds.append(new_thresh)
                                extra_labels.append(labels[idx])

    for remov in sorted(idx_del, reverse = True):
        del candidates[remov]
        del tests[remov]
        del labels[remov]
        del thresholds[remov]

    return(candidates, tests, labels, thresholds, extra_cands, extra_tests, extra_labels, extra_thresholds)

# CHECKING IF TWO UNGROUNDED AXIOMS ARE EQUAL OR A GENERAL\EXTENDED VERSION ONE ANOTHER REGARDLESS THE ORDER OF ITS LITERALS

def compare_axioms(axiom1, axiom2):
    literals1 = [lit.strip() for lit in re.split(':-|:\+|,(?![^(]*\))', axiom1.strip('.'))]
    expressions1 = [lit.strip() for lit in re.split(':-|:\+|,(?![^(]*\))', re.sub('\+','\+',re.sub('[A-Z][0-9]?', '[A-Z][0-9]?', re.sub('\)','\)',re.sub('\(','\(', axiom1.strip('.'))))))]
    literals2 = [lit.strip() for lit in re.split(':-|:\+|,(?![^(]*\))', axiom2.strip('.'))]
    expressions2 = [lit.strip() for lit in re.split(':-|:\+|,(?![^(]*\))', re.sub('\+','\+',re.sub('[A-Z][0-9]?', '[A-Z][0-9]?', re.sub('\)','\)',re.sub('\(','\(', axiom2.strip('.'))))))]
    intersection = [key for key in expressions1 if key in expressions2]
    var1 = []
    var2 = []
    for lit_expression in intersection:
        var1.extend([re.findall('[A-Z][0-9]?', literal) for literal in re.findall(lit_expression, axiom1)][0])
        var2.extend([re.findall('[A-Z][0-9]?', literal) for literal in re.findall(lit_expression, axiom2)][0])
             
    i1 = [[i for i, v1 in enumerate(var1) if var1[i] == a] for a in var1]
    i2 = [[i for i, v2 in enumerate(var2) if var2[i] == a] for a in var2]
    
    if i1 != i2:
        equal = 0
        version = 0
    else:
        equal = 1 if set(expressions1) == set(expressions2) else 0
        version = 0
        if expressions1[0] == expressions2[0]:
            version = 1 if ([n for n in expressions1 if n in expressions2] == expressions1) or ([n for n in expressions2 if n in expressions1] == expressions2) else 0
    return [equal, version]



# main...

#set of possible actions, objects and places


Objects = ['green_cube_large', 'white_can_small', 'red_cube_large', 'yellow_cube_large', 'blue_ball', 'pitcher', 'yellow_duck',  'white_cube_large']
Places = ['green_cube_large', 'white_can_small', 'red_cube_large', 'yellow_cube_large', 'white_cube_large', 'table']
Actions = ['pickup', 'putdown']
Relations = ['front', 'behind', 'above', 'below', 'left', 'right', 'touch', 'not_touch', 'far', 'on']
ObjPlaces = list(set(Objects) | set(Places)) # Objects + Places - intersection
Robot = ['rob1']
Sorts = [['O',ObjPlaces], ['R',Robot]]

missing_axioms = ['-occurs(pickup(R, A), I) :- holds(relation(below, A, B), I).','-occurs(pickup(R, O1), I) :- holds(in_hand(R, O2), I).', '-occurs(putdown(R, O, L), I) :- -holds(in_hand(R,O), I).' , 'holds(in_hand(R, O), I+1) :- occurs(pickup(R, O), I).', '-holds(in_hand(R, O), I+1) :- occurs(putdown(R, O, L), I).']

##########    EXPERIMENTS     ########

TPf = TPvf = FPf = FPvf = FNf = FNvf = 0
falsePositive = []
falsePositiveV = []

for _ in range(20):

###   Run different actions in different initial states ...

	copyfile('ASP_agent_with(out).sp', 'agent_learner.sp')

	stop2 = 0

	discovered_axioms = []
	 

	while stop2 < 10:
        
		unexpected = []
		extra = []

		stop1 = 0
		while not unexpected and not extra and stop1 < 100:
		    stop1 += 1
		    objects = Objects[:]
		    places = Places[:]
		    action = random.choice(Actions)
		    initialState, actionGround = randomState_Action(action, objects, places)
		    planner('ASP_agent_oracle.sp', actionGround, initialState, 'AnswerSetObs')
		    planner('agent_learner.sp', actionGround, initialState, 'AnswerSetExp')
		    
		    # ... until find an inconsistency between observation and expectation:
		    unexpected, extra = compareAnsSet('AnswerSetExp', 'AnswerSetObs')
		    
		if stop1 >= 100:
		    break   
		### After finding any incompatibility, execute the same action for different arguments and initial states, and store the relevant information for the decision tree induction

		train_amount = 100

		count_unexp = 0
		count_extra = 0
		positive_extra = 0
		positive_unexp = 0
		causal_law = []
		execut_cond = []
		AllRelevantFacts = []
		relevantTerms = []
		unexpect_lit = []


		while count_unexp < train_amount and count_extra < train_amount:  
		    objects = Objects[:]
		    places = Places[:]
		    initialState, actionGround = randomState_Action(action, objects, places)
		    planner('ASP_agent_oracle.sp', actionGround, initialState, 'AnswerSetObs')
		    planner('agent_learner.sp', actionGround, initialState, 'AnswerSetExp')
		    unexpected, extra = compareAnsSet('AnswerSetExp', 'AnswerSetObs')
		    # finding the relevant facts 
		    relevantFacts, relevantTerms = relevantInfo(actionGround, 'AnswerSetExp', Relations, relevantTerms)       
		    # WHAT ABOUT THE CASES WHEN THERE ARE MULTIPLE INCONSISTENCIES?????        
		    if unexpected and positive_unexp < 0.6*train_amount:
			print 'unexpected'
			causal_law.append([unexpected, [actionGround], relevantFacts, 1])
			count_unexp += 1
			positive_unexp += 1
			if count_extra < 0.4*train_amount or positive_extra >= 0.6*train_amount:
			    execut_cond.append([[], [actionGround], relevantFacts, 0]) 
			    count_extra += 1 
			      
		    elif extra and positive_extra < 0.6*train_amount:
			print 'extra'
			if os.lstat('AnswerSetObs').st_size > 5:
			    execut_cond.append([extra, [actionGround], relevantFacts, 1])
			else:
			    execut_cond.append([[], [actionGround], relevantFacts, 1])
			count_extra += 1
			positive_extra += 1
		    else:
			print 'consistent'
			if count_unexp < 0.4*train_amount or positive_unexp >= 0.6*train_amount:
			    causal_law.append([unexpected, [actionGround], relevantFacts, 0])
			    count_unexp += 1
			if count_extra < 0.4*train_amount or positive_extra >= 0.6*train_amount:
			    if os.lstat('AnswerSetObs').st_size > 5:    
				execut_cond.append([extra, [actionGround], relevantFacts, 0])
			    else:
				execut_cond.append([[], [actionGround], relevantFacts, 0])
			    count_extra += 1
		causal_input = []
		executability_input = []


		if count_unexp == train_amount:
		    causal_law, AllRelevantFacts = relRepresentation(causal_law)
		    unexpect_lit = collections.Counter([causal[0][0] for causal in causal_law if causal[0]])
		    # sorting the list for saving in the csv file
		    AllRelevantFacts.extend(['inconsitent'])
		    causal_input.append(AllRelevantFacts)#.extend(['inconsitent'])) #creating the label column

		    for causal_event in causal_law:
			new_line = []
			for fact in AllRelevantFacts[:-1]:
			   if fact in causal_event[2]:
			       new_line.append(1)
			   else:
			       new_line.append(0)
			new_line.append(causal_event[-1]) # fill in the label value
			causal_input.append(new_line)
		    # save causal law in a ".csv" file
		    with open('treeInput.csv', 'w') as tree_input:
			wr = csv.writer(tree_input, quoting=csv.QUOTE_ALL)
			for causal_line in causal_input:
			    wr.writerow(causal_line)
		    #print unexpect_lit
		    # saving the relevant data for axioms construction in the tree induction algorithm
		    print unexpect_lit
		    print unexpect_lit.values()
		    if len(unexpect_lit) > 1:
			var = re.findall('[A-Z][0-9]?', causal_law[-1][1][0])
			tot_vars = []
			for unexp in unexpect_lit.keys():
			    tot_vars.append(sum([v in unexp for v in var])) 
			unexp_literal = unexpect_lit.keys()[tot_vars.index(max(tot_vars))]
		    else:
		        unexp_literal = unexpect_lit.keys()[0]
		    info = ['causal_law', [unexp_literal], [causal_law[-1][1][0].replace('.','')], (len(AllRelevantFacts) - 1)]
		    print info
		    
		else:
		    execut_cond, AllRelevantFacts = relRepresentation(execut_cond)
		    # sorting the list for saving in the csv file
		    AllRelevantFacts.extend(['inconsitent'])
		    executability_input.append(AllRelevantFacts)
		    for executability_event in execut_cond:
			new_line = []
			for fact in AllRelevantFacts[:-1]:
			   if fact in executability_event[2]:
			       new_line.append(1)
			   else:
			       new_line.append(0)
			new_line.append(executability_event[-1]) # fill in the label value
			executability_input.append(new_line)
		
		    # save causal law in a ".csv" file
		    with open('treeInput.csv', 'w') as tree_input:
			wr = csv.writer(tree_input, quoting=csv.QUOTE_ALL)
			for execut_line in executability_input:
			    wr.writerow(execut_line)
		    
		    info = ['executability_cond', [], [execut_cond[-1][1][0].replace('.','')], (len(AllRelevantFacts) - 1)]
		    print info
		    #with open('parse.txt', 'wb') as lst:
		    #    pickle.dump(info, lst)
	

		stop2 += 1
		   

	######## TRAINING THE DECISION TREE ###############################################
	# loading data from robot simulation


		#importing the data from .CSV file
		dataset = pd.read_csv('treeInput.csv')
		n_features = info[-1]
		test_size = 0.05
		n_trees = 100

		level = 0.98

		feature_names = dataset.columns.tolist()[:n_features]
		classes_names = dataset.columns.tolist()[n_features:]

		if len(feature_names) > 0:
		
		#for level in levels:

		  literals = []
		  count_lit = []
		  negs = []
		  threshols = []
		  for idn, class_name in enumerate(classes_names):
		    for it in range(n_trees):

		      #formating the input
		      train_features, X_test, train_targets, X_label = train_test_split(dataset.iloc[:,:n_features], dataset.iloc[:,n_features+idn], test_size=test_size)

		      #inducting the decision tree
		      tr = DecisionTreeClassifier(criterion = 'entropy',min_samples_split=15, min_samples_leaf=5).fit(train_features,train_targets)

		      #exporting the tree
		      tree.export_graphviz(tr,out_file='tree_'+class_name+'.dot',feature_names=feature_names,proportion=False,leaves_parallel=True,precision=2)#,class_names=['stable/non-occluded','stable/occluded','unstable/non-occluded','unstable/occluded'])

		      #checking which features are binary or not
		      feature_type = []
		      for feature in feature_names:
			if max([int(f) for f in X_test.iloc[:][feature]]) > 1:
			  feature_type.append('not')
			else:
			  feature_type.append('bin')

		  # The decision estimator has an attribute called tree_  which stores the entire
		  # tree structure and allows access to low level attributes. The binary tree
		  # tree_ is represented as a number of parallel arrays. The i-th element of each
		  # array holds information about the node `i`. Node 0 is the tree's root. NOTE:
		  # Some of the arrays only apply to either leaves or split nodes, resp. In this
		  # case the values of nodes of the other type are arbitrary!
		  #
		  # Among those arrays, we have:
		  #   - left_child, id of the left child of the node
		  #   - right_child, id of the right child of the node
		  #   - feature, feature used for splitting the node
		  #   - threshold, threshold value at the node
		  #

		  # Using those arrays, we can parse the tree structure:

		      n_nodes = tr.tree_.node_count
		      children_left = tr.tree_.children_left
		      children_right = tr.tree_.children_right
		      feature = tr.tree_.feature
		      threshold = tr.tree_.threshold
		      value = tr.tree_.value

		      samples_tot = np.sum(value[0])
		      print("Total samples = %s." % samples_tot)

		      # The tree structure can be traversed to compute various properties such
		      # as the depth of each node and whether or not it is a leaf.
		      node_depth = np.zeros(shape=n_nodes, dtype=np.int64)
		      is_leaves = np.zeros(shape=n_nodes, dtype=bool)
		      stack = [(0, -1)]  # seed is the root node id and its parent depth
		      while len(stack) > 0:
			node_id, parent_depth = stack.pop()
			node_depth[node_id] = parent_depth + 1

			# If we have a test node
			if (children_left[node_id] != children_right[node_id]):
			  stack.append((children_left[node_id], parent_depth + 1))
			  stack.append((children_right[node_id], parent_depth + 1))
			else:
			  is_leaves[node_id] = True

		      print("The binary tree structure has %s nodes and has "
			  "the following tree structure:"
			  % n_nodes)
		      for i in range(n_nodes):
			if is_leaves[i]:
			  print("%snode=%s leaf node, with number of samples = %s, and values = %s" % (node_depth[i] * "\t", i, np.argmax(value[i]), value[i]))
			else:
			  print("%snode=%s test node: go to node %s if not %s else to "
				"node %s."
				% (node_depth[i] * "\t",
				   i,
				   children_left[i],
				   feature_names[feature[i]],
				   children_right[i],
				   ))
		      print("End of tree %s" % idn)
		      
		      
		      
		############## CREATING CANDIDATE AXIOMS:  ####################################


		    # First let's retrieve the decision path of each sample. The decision_path
		    # method allows to retrieve the node indicator functions. A non zero element of
		    # indicator matrix at the position (i, j) indicates that the sample i goes
		    # through the node j.

		      node_indicator = tr.decision_path(X_test)

		    # Similarly, we can also have the leaves ids reached by each sample.

		      leave_id = tr.apply(X_test)

		    # Now, it's possible to get the tests that were used to predict a sample or
		    # a group of samples. Let's make it for all samples in the test data.

		      att_branches = []
		      candidates = []
		      labels = []
		      tests = []
		      thresholds= []

		      #building the candidates based on if they have at least one example suporting it and if the corresponding leaf agree (in some minimum percentage - 95% in this example) with its label. Also if this leaf contains a representative percentage of training examples (e.g. 3%).

		      for sample_id in range(len(X_test)):
			node_index = node_indicator.indices[node_indicator.indptr[sample_id]:
				                      node_indicator.indptr[sample_id + 1]]
				                      
			new_branch = 0
			if (list(node_index) not in [list(item) for item in att_branches]):
			  new_branch = 1
			  att_branches.append(node_index)

			#print('Rules used to predict sample %s: %s' % (sample_id, node_index))
			for node_id in node_index:
			    if leave_id[sample_id] == node_id:
			      #print("leaf id node %s" % node_id)
			      if ((np.max(value[node_id])/np.sum(value[node_id])) > level) and ((np.sum(value[node_id])/samples_tot) > 0.02):
			      # if the conditions of at least 95% of samples suporting a class and minimum of 2% of the total in a leaf, the branch is considered for providing candidates
				if new_branch:
				    # building candidates from this branch
				    cands = (math.pow(2, len(node_index[:-1]))-1) #if len(node_index[:-1]) < 4 else math.pow(2, len(node_index[:-1])-1)
				    # Number of candidates proportional to the number of nodes. With "n" being the number of nodes, for n = 1, 2, 3, cands = 2^n - 1 (number of possible combinations), otherwise cands = 2^(n-1).
				    all_cands = []
				    for j in range(len(node_index[:-1])):
				        all_cands.extend(list(itertools.combinations(sorted(node_index[:-1]), j+1)))
				    for k in range(int(cands)):
				        # drawing cadidates from the branch (excluding the leaf)
				        idx_cand = np.random.choice(len(all_cands))
				        candidate = all_cands[idx_cand]
				        all_cands.remove(candidate)
				        lab = np.argmax(value[node_id])
				        if (list(candidate) not in [list(item) for item in candidates]) and lab == 1:
				            # if the candidate is not in the list, it is included:
				            candidates.append(candidate) # -nodes in candidate
				            labels.append(np.argmax(value[node_id])) # -labels supported by the leaf
				            tests.append([X_test.iloc[sample_id][feature_names[feature[item]]] for item in candidate]) # -the test performed in each node (True or False)  
				            thresholds.append([threshold[h] for h in candidate])         
			      continue


		      candidates, tests, labels, thresholds, extra_cands, extra_tests, extra_labels, extra_thresholds = filter_cands(X_test, candidates, tests, labels, thresholds, level)     

		      if len(extra_cands) > 0:
			candidates.extend(extra_cands)
			tests.extend(extra_tests)
			labels.extend(extra_labels)
			thresholds.extend(extra_thresholds)
			candidates, tests, labels, thresholds,extra_cands, extra_tests, extra_labels, extra_thresholds = filter_cands(X_test, candidates, tests, labels, thresholds, level)

		      #printing the final results
		      
		      # labels = {1: "inconsistent", 0: "consistent"}
		      # heads = {1: -'action': for executability condition; 2. 'unexpected fluent' (I + 1): for causal laws}
		      # bodies = {1: precondition extract form decision tree: for executability condition; 2. 'action' (+ precondition from decision tree): for causal laws} 
		      if info[0] == 'executability_cond':
			  print("     EXECUTABILITY CONDITIONS:     ")
			  for idx, candidate in enumerate(candidates):
			      literal = []
			      neg = []
			      threshol = []
			      sys.stdout.write("-")
			      neg.append(0) 
			      sys.stdout.write(re.sub(',\n?[0-9]\)',',I)',info[2][0]))
			      literal.append(re.sub(',\n?[0-9]\)',',I)',info[2][0]))
			      threshol.append(0) # ?????????
			      sys.stdout.write(":-")
			      for idc,axiom in enumerate(candidate):
				  literal.append(feature_names[feature[axiom]])
				  if feature_type[feature[axiom]] == 'bin':
				      if tests[idx][idc] == 0:
				          sys.stdout.write("-")
				      neg.append(tests[idx][idc])
				      sys.stdout.write(re.sub(',\n?[0-9]\)',',I)',feature_names[feature[axiom]]))
				  #else:
				  #    sys.stdout.write(feature_names[feature[axiom]])
				  #    if tests[idx][idc] > thresholds[idx][idc]:
				  #        sys.stdout.write(">")
				  #        neg.append(1)
				  #    else:
				  #        sys.stdout.write("<=")
				  #         neg.append(0)
				  #    sys.stdout.write(str(int(thresholds[idx][idc])))
				  threshol.append(int(thresholds[idx][idc])) ## ??????????
				  if idc < (len(candidate)-1):
				      sys.stdout.write(",")
			      print "."
			      if literal in literals: 
				  for i in [indx for indx, x in enumerate(literals) if x == literal]: 
				      if neg == negs[i] and threshol == threshols[i]:
				          count_lit[i] += 1
			      else:
				  literals.append(literal)
				  count_lit.append(1)
				  negs.append(neg)
				  threshols.append(threshol)
			    
		      else: # info[0] == 'causal_law'
			  print("     CAUSAL LAWS:     ")
			  for idx, candidate in enumerate(candidates):
			      literal = []
			      neg = []
			      threshol = []
			      sys.stdout.write(re.sub(',\n?[0-9]\)',',I+1)',info[1][0]))
			      literal.append(re.sub(',\n?[0-9]\)',',I+1)',info[1][0]))
			      neg.append(1)
			      sys.stdout.write(":-")
			      sys.stdout.write(re.sub(',\n?[0-9]\)',',I)',info[2][0]))
			      literal.append(re.sub(',\n?[0-9]\)',',I)',info[2][0]))
			      threshol.append(0) # ?????????
			      neg.append(1)
			      if not candidate:
				  sys.stdout.write(".")
			      else:
				  sys.stdout.write(",")    
				  for idc,axiom in enumerate(candidate):
				      literal.append(feature_names[feature[axiom]])
				      if feature_type[feature[axiom]] == 'bin':
				          if tests[idx][idc] == 0:
				              sys.stdout.write("-")
				          neg.append(tests[idx][idc])
				          sys.stdout.write(re.sub(',\n?[0-9]\)',',I)',feature_names[feature[axiom]]))
				      threshol.append(int(thresholds[idx][idc])) ## ??????????
				      if idc < (len(candidate)-1):
				          sys.stdout.write(",")
				  print "."
				  if literal in literals: 
				      for i in [indx for indx, x in enumerate(literals) if x == literal]: 
				          if neg == negs[i] and threshol == threshols[i]:
				              count_lit[i] += 1
				  else:
				      literals.append(literal)
				      count_lit.append(1)
				      negs.append(neg)
				      threshols.append(threshol)
				  
		  print level
		  print literals
		  print count_lit
		  
		  new_axiom = []
		
		else:
		    literals = []
		  
		f = open("axioms_%.2f.txt" % level, "w+")
		if not literals and info[0] == 'causal_law':
		      f.write(re.sub(',\n?[0-9]\)',',I+1)',info[1][0]))
		      new_ax = re.sub(',\n?[0-9]\)',',I+1)',info[1][0])
		      f.write(":-")
		      new_ax = new_ax + ':-'
		      f.write(re.sub(',\n?[0-9]\)',',I)',info[2][0]))
		      new_ax = new_ax + re.sub(',\n?[0-9]\)',',I)',info[2][0])
		      f.write(".\n")
		      new_ax = new_ax + '.'
		      new_axiom = [new_ax]
		  
		if info[0] == 'executability_cond' and count_lit:
		      n = max(count_lit)
		else:
		      n = 0.4*n_trees
		      
		for idx, candidate in enumerate(literals):
		    if count_lit[idx] >= n:
		      new_ax = ''
		      if negs[idx][0] == 0:
			f.write("-")
			new_ax = new_ax + '-'
		      f.write(candidate[0])
		      new_ax = new_ax + candidate[0]
		      f.write(":-")
		      new_ax = new_ax + ':-'
		      for ind, prop in enumerate(candidate[1:]):
			if negs[idx][ind+1] == 0:
			    f.write("-")
			    new_ax = new_ax + '-'
			f.write(re.sub(',\n?[0-9]\)',',I)',prop))
			new_ax = new_ax + re.sub(',\n?[0-9]\)',',I)',prop)
			if ind < (len(candidate)-2):
			    f.write(",")
			    new_ax = new_ax + ','
		      f.write(".\n")
		      new_ax = new_ax + '.'
		      new_axiom.append(new_ax)
		f.close()

                if new_axiom:
                      discovered_axioms.extend(new_axiom)

		writer('agent_learner.sp', 'axioms_'+str(level)+'.txt')
		

	#########################################################################################################

		print count_unexp
		print count_extra
		print stop1
		print stop2
		
		# Computing Precison and recall
		# Considering only idnetical axioms
		missing_axioms = [miss.replace(' ','') for miss in missing_axioms]
		print missing_axioms
		print discovered_axioms
		
		TP = sum([any([compare_axioms(found, true)[0] for true in missing_axioms]) for found in discovered_axioms])

		TPv = min(len(missing_axioms), sum([any([compare_axioms(found, true)[0] or compare_axioms(found, true)[1] for true in missing_axioms]) for found in discovered_axioms]))

		FP = sum([all([not compare_axioms(found, true)[0] for true in missing_axioms]) for found in discovered_axioms])

		FPv = sum([all([not (compare_axioms(found, true)[0] or compare_axioms(found, true)[1]) for true in missing_axioms]) for found in discovered_axioms])

		FN = sum([all([not compare_axioms(found, true)[0] for found in discovered_axioms]) for true in missing_axioms])

		FNv = sum([all([not (compare_axioms(found, true)[0] or compare_axioms(found, true)[1]) for found in discovered_axioms]) for true in missing_axioms])
                
                false_pos =[]
                false_posV = []
                for found in discovered_axioms:
                    if all([not compare_axioms(found, true)[0] for true in missing_axioms]):
                        false_pos.append(found)
                    if all([not (compare_axioms(found, true)[0] or compare_axioms(found, true)[1]) for true in missing_axioms]):
                        false_posV.append(found)
                    
        falsePositive.extend(false_pos)   
        falsePositiveV.extend(false_posV)
	TPf += TP
	TPvf += TPv
	FPf += FP
	FPvf += FPv
	FNf += FN
	FNvf += FNv  
	print TPf
	print TPvf  
	print FPf
	print FPvf
	print FNf
	print FNvf
	print missing_axioms
	print discovered_axioms
	
	print '@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@'
	print '@                            #############                                                   @'
	print '@                                #####                                                       @'
	print '@                                #####                                                       @'
	print '@                                #####                                                       @'
	print '@                                #####                                                       @'
	print '@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@'

print float(TPf/(TPf+FPf))
print float(TPf/(TPf+FNf))
print float(TPvf/(TPvf+FPvf))
print float(TPvf/(TPvf+FNvf))

print falsePositive
print falsePositiveV

