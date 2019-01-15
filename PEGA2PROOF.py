
# coding: utf-8

# In[317]:

#Viktor Rumanuk
#vrumanuk@gmail.com

import sys

#Remove doublecuts
#Ideally this is not needed but the proof checker does some
#automatic consolidation of negatives and I wanted to avoid corner cases due to both programs conflicting
def doublecut_reduce(term):
    prev = []
    nest = 0
    #Simply step through every character in the string, keeping track of depth, and remove any double sets of parentheses
    for n, c in enumerate(term):
        if c == '(':
            prev.append(n)
            nest += 1
        elif c == ')':
            nest -= 1
            if prev[-1] > 0 and term[prev[-1]-1] == '(' and n < (len(term)-1) and term[n+1] == ')':
                if nest == 1:
                    term = term[:prev[-1]-1] + '[' + term[prev[-1]+1:n] + ']' + term[n+2:]
                else:
                    term = term[:prev[-1]-1] + term[prev[-1]+1:n] + term[n+2:]
                term = doublecut_reduce(term)
                break
            prev = prev[:-1]
    
    return term

#Splits a PEGA string into separate terms
#Each term returned corresponds to a separate top-level cut of data in the EG proof
def separate_parens(term):
    seps = [0]
    nest = 0
    #Very similar to DoubleCutReduce: We just walk through the string and track when we "resurface" to depth 0
    for n, c in enumerate(term):
        if c == '(' and nest == 0 and n != 0:
            seps.append(n)
            nest += 1
        elif c == '(':
            nest += 1
        elif c == ')' and nest == 1:
            nest = 0
            seps.append(n+1)
        elif c == ')':
            nest -= 1

    fseps = []
    for n in range(len(seps)-1):
        if seps[n] != seps[n+1]:
            fseps.append(seps[n])
    
    fseps.append(seps[-1])
        
    split = [term[fseps[i]:fseps[i+1]] for i in range(len(fseps)-1)]
    if fseps[-1] != len(term):
        split.append(term[fseps[-1]:])
    return split

#Helper function that removes extra identifiers I used during double cut reduction
#These existed to prevent the program from "losing" a term from one step of the proof to the next due to new variables
#appearing on the canvas as the result of a double cut reduction
def brace_split(line):
    final_line = []
    
    for t in line:
        nt = ""
        l = t.find('[')
        r = t.find(']')
        
        if l != -1 and r != -1:
            final_line.append(t[:l])
            final_line.append(t[l+1:r])
            final_line.append(t[r+1:])
        else:
            nt = t.replace('[', '')
            nt = nt.replace(']', '')
        
            if len(nt) > 0:
                final_line.append(nt)
    
    final_line = [x for x in final_line if len(x) > 0]
    return final_line
                

#Explicitly apply negation and insert correct connective between variables based on depth
def apply_cut(term):
    depth = 0
    nt = ""
    n = 0
    while n < len(term):
        c = term[n]
        if c == '(':
            depth += 1
            if term[n+3] != ')':
                nt += c
        elif c == ')':
            depth -=1
            if term[n-3] != '(':
                nt += c
            if n < len(term)-1 and term[n+1] != ')':
                if depth % 2 == 0:
                    nt += " & "
                else:
                    nt += " | "
        elif c == '|':
            if n < len(term)-1 and term[n+1] != ')':
                if depth % 2 == 0:
                    nt += " & "
                else:
                    nt += " | "
        else:
            if depth % 2 == 1:
                nt += "!"
            
            nt += c
        
        n += 1
    
    if nt[0] == '(' and nt[-1] == ')':
        return nt[1:-1]
    
    return nt

#Returns a list of tuples where each tuple describes the alteration that occurred
#on the changing term for each line in the proof
def get_deltas(lines):
    return [(list(set(lines[n]) - set(lines[n+1]))[0], list(set(lines[n+1]) - set(lines[n]))[0]) for n in range(len(lines)-1)]

#Find the line in the proof that we need to reference for the current proof step
def find_line(ts, targ):
    #Ignore double negatives
    if targ[0] == '!' and targ[1] == '!':
        targ = targ[2:]
    
    for n, c in enumerate(ts):
        if c == targ:
            return n+1
    
    print "FAILED TO FIND REFERENCE"

#Generates the proof!
def get_prooflines(ts, blob, premisecount):
    prooflines = []
    
    for d in blob:
        delt = d[0]
        op = d[1]
        pl = ""
        
        #Line generation is based on which operation took place in the EG proof
        if op == "ER:":
            #Erasure is simply a 'simplification' operation wherein a conjuction is removed from
            pl = "lin " + delt[1] + ":Simplification: " + str(find_line(ts, delt[0]))
        elif op == "IN":
            #Insertion is simply an 'addition' operation wherein a disjunction is added to
            pl = "lin " + delt[1] + ":Addition: " + str(find_line(ts, delt[0]))
        else:
            #Iteration! We use either Modus Ponens or Modus Tollens
            ponens = True
            if len(delt[0]) > len(delt[1]):
                if delt[0].find(delt[1]) == 0:
                    ponens = False
                diff = delt[0].replace(delt[1], "")
            else:
                diff = delt[1].replace(delt[0], "")

            diff = diff.replace(" | ", "")
            diff = diff.replace(" & ", "")
            diff = diff.replace("()", "")
            
            #Decide between Modus Ponens and Modus Tollens based on
            #whether the beginning or the end of the disjunction was removed during the relevant EG proof step
            #Ponens vs Tollens just decides how to structure the implication we construct
            #I did it this way because it is extremely tedious to justify to Mike Usher's program
            #that (A or B) or C == (C or B) or A
            if ponens:
                implication = "!" + diff + ">(" + delt[1].replace(" ", "") + ")"
                pl = "lin " + implication + ":Implication: " + str(find_line(ts, delt[0]))
                ts.append(implication)
                prooflines.append(pl)
                pl = "lin " + delt[1].replace(" ", "") + ":Modus Ponens: " + str(find_line(ts, "!" + diff)) + " " + str(len(prooflines)+premisecount)
            else:
                implication = "!(" + delt[1].replace(" ", "") + ")>" + diff
                pl = "lin " + implication + ":Implication: " + str(find_line(ts, delt[0]))
                ts.append(implication)
                prooflines.append(pl)
                pl = "lin " + delt[1].replace(" ", "") + ":Modus Tollens: " + str(find_line(ts, "!" + diff)) + " " + str(len(prooflines)+premisecount)
        
        #Make sure to update list of current knowns
        ts.append(delt[1])
        prooflines.append(pl)
    
    return prooflines

def main(path):
    with open (path, "r") as pega:
        lines=pega.read().split("\n")[:-1]
    
    #Pull in PEGA data line by line and format away unnecessary characters
    lines = [''.join(c for c in line if c not in '[]-./').upper() for line in lines]
    lines = [x for x in lines if x != '\r']
    if lines[0][-1] == '\r':
        lines = [x[:-1] for x in lines]
    
    #Store the operator portion of each line for later use
    operators = [x[:3] for x in lines]
    
    #Split the raw PEGA data into our desired format
    lines = [brace_split(separate_parens(doublecut_reduce(x[3:]))) for x in lines]
    
    #Remove cuts and replace with appropriate negation of term
    processed_lines = [[apply_cut(y) for y in x] for x in lines]
    line_nums = [0] + [n for n in range(1, len(processed_lines)) if processed_lines[n] != processed_lines[n-1]]
    processed_lines = [processed_lines[n] for n in range(len(processed_lines)) if n in line_nums]
    operators = [operators[n] for n in range(len(operators)) if n in line_nums]

    #Retrieve the changes that occurred between each line in the graph
    deltas = get_deltas(processed_lines)
    
    #Signify premises with the "pre" prefix
    premises = ["pre " + x.replace(" ", "") for x in list(set(processed_lines[0]))]
    
    #Store premises as knowns for use in generating the proof lines
    truths = list(set(processed_lines[0]))

    #Generate the lines of the proof
    proof_lines = get_prooflines(truths, zip(deltas, operators), len(premises))
    
    #Print the completed proof. This output can be fed into Mike Usher's
    #proof checker for verification of the original EG proof
    for p in premises:
        print p
    
    for l in proof_lines:
        print l

#main("proof2.pega")
if __name__ == "__main__":
    main(sys.argv[1])


# In[ ]:




# In[ ]:



