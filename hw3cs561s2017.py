import copy
import sys
import time

start_time = time.time()

inFile = open('input49.txt', 'r')
outFile = open('output.txt', 'w')
MAXLIM = 64000
myQueries = []
SEPARATOR = '\n'
myQuery = inFile.readline().strip(SEPARATOR)
while myQuery != '******':
    myQueries.append(myQuery)
    myQuery = inFile.readline().strip(SEPARATOR)

class MyNode(object):
    def p(self, v='', e={}):
        if self.type == 'decision':
            return 1.0

        for i in range(0, len(self.table)):
            matches = True
            for j in range(0, len(self.parents)):
                myVal = self.table[i][j+1]
                myParent = self.parents[j]
                if e[myParent] != myVal:
                    matches = False
                    break
            if matches:
                if v == '-':
                    return 1.0 - self.table[i][0]
                elif v == '+':
                    return self.table[i][0]

    def __init__(self, name='', parents=[], table=[]):
        self.parents = parents
        self.type = ''
        self.table = table
        self.name = name

def outputLine(qType='', val=0.0, meuValues=[]):
    if qType == 'EU':
        outFile.write(str(int(round(val))))
    elif qType == 'MEU':
        meu_str = ''
        for meuVal in meuValues:
            meu_str += meuVal + ' '
        outFile.write(meu_str + str(int(round(val))))
    elif qType == 'P':
        outFile.write("%.2f" %round(val, 2))

class MyNetwork(object):
    def is_decision_node(self, name=''):
        node = self.get_node(name)
        return node.type == 'decision'

    def get_node(self, name=''):
        index = self.vars.index(name)
        return self.nodes[index]

    def add_node(self, node=MyNode()):
        self.nodes.append(node)
        self.vars.append(node.name)

    def __init__(self):
        self.utility = None
        self.nodes = []
        self.vars = []

def getTfVals(len, myNum):
    myVals = []
    for i in range(0, len):
        if (myNum >> i) & 1 == 0:
            myVals.append('+')
        else:
            myVals.append('-')
    return myVals

def trimBayNet(bayNet=MyNetwork(), query=''):
    trimmedBayNet = copy.deepcopy(bayNet)
    temp = query.split('(')
    temp[1] = temp[1].strip(')')
    maxIndex = 0
    varList = []
    temp = temp[1].split(' | ')
    ls = temp[0].split(', ')
    for l in ls:
        varList.append(l.split(' = ')[0])

    if(len(temp) > 1):
        vars = temp[1].split(', ')
        for l in vars:
            varList.append(l.split(' = ')[0])

    for var in varList:
        if maxIndex < trimmedBayNet.vars.index(var):
            maxIndex = trimmedBayNet.vars.index(var)

    if maxIndex > 0:
        if maxIndex > 20:
            maxIndex = 19
        del trimmedBayNet.vars[(maxIndex+1):]
        del trimmedBayNet.nodes[(maxIndex+1):]
    return trimmedBayNet;


def enumerationAsk(bayNet=MyNetwork(), X={}, e={}):
    myKeys = X.keys()
    myArray = []
    myIndex = 0
    for v in myKeys:
        if e.__contains__(v):
            if e[v] == X[v]:
                X.__delitem__(v)
            else:
                return 0.0
    xLen = len(X)
    for i in range(0, 2 ** xLen):
        vals = getTfVals(xLen, i)
        matches = True
        sx = copy.deepcopy(e)
        for j in range(0, xLen):
            key = X.keys()[j]
            sx[key] = vals[j]
            if vals[j] != X[key]:
                matches = False
        if matches:
            myIndex = i
        enumAll = enumerateAll(bayNet, bayNet.vars, sx)
        myArray.append(enumAll)
    norm = myArray[myIndex] / sum(myArray)
    return norm

def meuEnumerateAll(bayNet=MyNetwork(), X=[], e={}):
    max = -MAXLIM
    xLen = len(X)
    maxVals = []
    for i in range(0, 2 ** xLen):
        si = copy.deepcopy(e)
        vals = getTfVals(xLen, i)
        for j in range(0, xLen):
            si[X[j]] = vals[j]
        tempMax = euEnumerateAll(bayNet, si)
        if(tempMax > max):
            max = tempMax
            maxVals = vals
    return  max, maxVals

def euEnumerateAll(bayNet=MyNetwork(), e={}):
    total = 0.0
    uNode = bayNet.utility
    uTables = uNode.table
    uParents = uNode.parents
    for uTable in uTables:
        X = {}
        for j in range(0, len(uParents)):
            X[uParents[j]] = uTable[j+1]
        total += enumerationAsk(bayNet, X, e) * uTable[0]
    return total

def enumerateAll(bayNet=MyNetwork(), vars=[], e={}):
    if len(vars) == 0:
        return 1.0
    var = vars[0]
    myNode = bayNet.get_node(var)
    if var in e.keys():
        return myNode.p(e[var], e) * enumerateAll(bayNet, vars[1:], e)
    else:
        eVarFalse = copy.deepcopy(e)
        eVarFalse[var] = '-'
        eVarTrue = copy.deepcopy(e)
        eVarTrue[var] = '+'
        return myNode.p('-', e) * enumerateAll(bayNet, vars[1:], eVarFalse) + myNode.p('+', e) * enumerateAll(bayNet, vars[1:], eVarTrue)

def askQuery(bayNet=MyNetwork(), query=''):
    temp = query.split('(')
    temp[1] = temp[1].strip(')')
    if temp[0] == 'EU':
        e = {}
        temp = temp[1].split(' | ')
        if(len(temp) > 1):
            temp[0] = temp[0] + ', ' + temp[1]
        myVars = temp[0].split(', ')
        for myVar in myVars:
            myVar = myVar.split(' = ')
            e[myVar[0]] = myVar[1]
        euEnumAll = euEnumerateAll(bayNet, e)
        outputLine('EU', euEnumAll)

    elif temp[0] == 'MEU':
        e = {}
        temp = temp[1].split(' | ')
        myVars = []
        lenS = temp[0].split(', ')
        for le in lenS:
            myVars.append(le)
        if(len(temp) == 2):
            rs = temp[1].split(', ')
            for rs in rs:
                t = rs.split(' = ')
                e[t[0]] = t[1]
        meu, meuValues = meuEnumerateAll(bayNet, myVars, e)
        outputLine('MEU', meu, meuValues)

    elif temp[0] == 'P':
        if temp[0] == 'P':
            if ' | ' not in temp[1]:
                e = {}
                temp = temp[1].split(', ')
                for varSplit in temp:
                    varInfo = varSplit.split(' = ')
                    e[varInfo[0]] = varInfo[1]
                pEnumAll = enumerateAll(bayNet, bayNet.vars, e)

            else:
                X = {}
                e = {}
                temp = temp[1].split(' | ')
                leftSide = temp[0].split(', ')
                for leftVar in leftSide:
                    varInfo = leftVar.split(' = ')
                    X[varInfo[0]] = varInfo[1]
                vars = temp[1]
                rightSide = vars.split(', ')
                for rightVar in rightSide:
                    varInfo = rightVar.split(' = ')
                    e[varInfo[0]] = varInfo[1]
                pEnumAll = enumerationAsk(bayNet, X, e)
        outputLine('P', pEnumAll)

def main():
    origBayNet = MyNetwork()
    myQuery = inFile.readline().strip(SEPARATOR)
    while myQuery != '':
        tempS = myQuery.split(' ')
        name = tempS[0]
        parents = tempS[2:]
        table = []
        decision = False
        for i in range(0, 2 ** len(parents)):
            tempS = []
            tempS = inFile.readline().strip(SEPARATOR).split(' ')
            if(tempS[0] == 'decision'):
                decision = True
            else:
                tempS[0] = float(tempS[0])
            table.append(tempS)


        node = MyNode(name, parents, table)
        if(decision == True): node.type = 'decision'
        origBayNet.add_node(node)

        myQuery = inFile.readline().strip(SEPARATOR)
        if myQuery != '***':
            break
        myQuery = inFile.readline().strip(SEPARATOR)

    if myQuery == '******':
        tempS = inFile.readline().strip(SEPARATOR).strip(' ').split(' ')
        name = 'u_node'
        parents = tempS[2:]
        table = []
        for i in range(0, 2 ** len(parents)):
            tempS = []
            tempS = inFile.readline().strip(SEPARATOR).split(' ')
            tempS[0] = float(tempS[0])
            table.append(tempS)

        node = MyNode(name, parents, table)
        node.type = 'utility'
        origBayNet.utility = node
    write = True
    inFile.close()
    for que in myQueries:
        if not write:
            outFile.write(SEPARATOR)
        write = False
        if len(origBayNet.vars) > 15:
            trimmedBayNet = trimBayNet(origBayNet, que)
            askQuery(trimmedBayNet, que)
        else:
            askQuery(origBayNet, que)

main()
outFile.close()

print("--- %s seconds ---" % (time.time() - start_time))