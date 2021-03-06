import os
import time

import cProfile

# From http://minisat.se/downloads/MiniSat.pdf

# Positive literals given by 2x 
# Negative literals given by 2x+1

# In Dimacs, uses positive and negative

# lbool can be 1 (True) or -1(False) or 0 for undefined

def sign(lit):
    """Return if literal is complemented"""
    return lit&1

def lsign(lit):
    """Return LitTrue or LitFalse for this literal"""
    return 1-2*(lit&1)

def var(lit):
    return lit>>1

def lit(v):
    return v<<1

LitTrue = 1
LitUndefined = 0
LitFalse = -1

class VarOrder(object):
    """Returns unassigned variable with highest activity"""

    # TODO
    # switch to using priority queue (https://docs.python.org/2/library/heapq.html#priority-queue-implementation-notes)

    def __init__(self,solver):
        self.solver = solver

    def newVar(self):
        """Called when new variable is created"""
        pass # TODO
        
    def update(self,x):
        """Called when a variable has been increased in activity"""
        pass # TODO

    def updateAll(self):
        """Called when all activities have been modified"""
        pass # TODO
        
    def undo(self,x):
        """Called when variable is unbound"""
        pass # TODO - how to know when one is assigned?
        
    def select(self):
        """Called to select a new unassigned variable"""
        A=self.solver.assigns
        return max([(a,i) for i,a in enumerate(self.solver.activity) if A[i]==LitUndefined])[1]

        
class Solver(object):
    
    def __init__(self):
        self.have_called_simplify = False
        self.contradiction_found = False
        self.constrs = [] # List of problem constraints
        self.learnts = [] # List of learnt clauses
        self.cla_inc = 1 # Amount to bump with activity
        self.cla_decay = 0.9 # Decay factor for clause activity
        self.activity = [] # Variable activity
        self.watches = [] # Map literal ->list of constraints
        self.propQ = set() # Propagation queue
        self.assigns = [] #List of current assignments
        self.trail = [] # List of assignments in chronological order
        self.trail_lim = [] # Separator indices for different decision levels
        self.reason = [] # For each variable, the constraint that implied its value
        self.level = [] # Variable -> decision level
        self.root_level = 0
        self.order = VarOrder(self)

    def nVars(self):
        return len(self.assigns)

    def nAssigns(self):
        return len(self.trail)

    def nConstraints(self):
        return len(self.constrs)

    def nLearnts(self):
        return len(self.learnts)

    def value_var(self,x):
        return self.assigns[x]

    def value_lit(self,lit):
        return -self.assigns[var(lit)] if sign(lit) else self.assigns[var(lit)]

    def decisionLevel(self):
        return len(self.trail_lim)
        
    def newVar(self):
        index = self.nVars ()

        self.watches.append([])
        self.watches.append([])
        self.reason.append(None)
        self.assigns.append(LitUndefined)
        self.level.append(-1)
        self.activity.append(0)
        self.order.newVar()
        return index

    def addClause(self,literals):
        """Returns False if contradiction detected, or True if added"""
        r,out_clause=make_clause(self,literals,False)
        if out_clause:
            self.constrs.append(out_clause)
        return r

    def propagate(self):
        """Propagate all unit facts.

        Return None if successful, or a conflicting clause otherwise"""
        while self.propQ:
            litp = self.propQ.pop()
            tmp=self.watches[litp]
            self.watches[litp]=[]
            for i,cl in enumerate(tmp):
                if not cl.propagate(self,litp):
                    # Constraint is conflicting
                    # Copy remaining watches and return constraint
                    self.watches[litp].extend(tmp[i+1:])
                    self.propQ=set()
                    return cl

    def enqueue(self,litp,cfrom=None):
        """Put a new fact on propagation queue, and update variables value.

        Return False if a conflict arises.
        cfrom contains a reference to constraint from which p was propagated"""
        #pdb.set_trace()
        if self.value_lit(litp) != LitUndefined:
            return self.value_lit(litp) == LitTrue
        v = var(litp)
        self.assigns[v] = lsign(litp)
        self.level[v] = self.decisionLevel()
        self.reason[v] = cfrom
        self.trail.append(litp)
        self.propQ.add(litp)
        #print 'trail',len(self.trail)
        return True

    def analyze(self,confl):
        """Analyze a conflict clause and produce a reason clause.

        Undos part of the trail, not beyond the last decision level.
        Returns reason clause, backtrack level
        """
        seen=set()
        counter=0
        litp=LitUndefined
        p_reason=[]
        out_learnt=[None] # Leave room for the asserting literal
        out_btlevel = 0
        while 1:
            p_reason = confl.calcReason(self,litp)

            # Trace reason for p
            for litq in p_reason:
                v=var(litq)
                if v not in seen:
                    seen.add(v)
                    if self.level[v] == self.decisionLevel():
                        counter+=1
                    elif self.level[v] > 0: # Exclude variables from decision level 0
                        out_learnt.append(litq^1)
                        out_btlevel = max(out_btlevel,self.level[v])

            # Select next literal to look at
            while 1:
                litp = self.trail[-1]
                confl = self.reason[var(litp)]
                self.undoOne()
                if var(litp) in seen:
                    break
            counter -= 1
            if counter<=0:
                break
        out_learnt[0] = litp^1
        return out_learnt, out_btlevel

    def record(self,ps):
        """Record a clause and drive backtracking"""
        r,c = make_clause(self,ps,True)
        assert r # Cannot fail here
        assert self.enqueue(ps[0],c) # cannot fail here
        if c is not None:
            self.learnts.append(c)

    def undoOne(self):
        """Unbinds the last variable on the trail"""
        litp = self.trail.pop()
        x = var(litp)
        self.assigns[x] = LitUndefined
        self.reason[x] = None
        self.level[x] = -1
        self.order.undo(x)

    def assume(self,litp):
        """Returns FALSE if immediate conflict"""
        self.trail_lim.append(len(self.trail))
        return self.enqueue(litp)

    def cancel(self):
        """Revert to state before last push"""
        for c in range( len(self.trail) - self.trail_lim.pop() ):
            self.undoOne()

    def cancelUntil(self,level):
        """Cancels several levels of assumptions"""
        while self.decisionLevel() > level:
            self.cancel()

    def search(self,nof_conflicts,nof_learnts, var_decay=0.95, cla_decay=0.999):
        """Assumes and propagates until conflict is found.

        Learns conflict clause and backtracks.

        nof_conflicts is limit on maximum conflicts to find.
        Returns LitUndefined if solution not found in this limit.
        Set to 0 to have no limit.
        
        nof_learnts is maximum number of learnt clauses to keep.
        Calls reduceDB to remove half when limit is reached.
        Clauses that are currently the reason for a variable assignment
        are locked and cannot be removed."""
        conflictC = 0
        var_decay = 1. / var_decay
        cla_decay = 1. / cla_decay
        self.var_inc = 1.
        self.cla_inc = 1.
        self.model=[]
        while 1:
            confl = self.propagate()
            if confl:
                # Conflict
                conflictC += 1
                learnt_clause = []
                backtrack_level=[None]
                if self.decisionLevel() == self.root_level:
                    return LitFalse
                learnt_clause,backtrack_level = self.analyze(confl)
                self.cancelUntil(max(backtrack_level,self.root_level))
                self.record(learnt_clause)
                self.decayActivities()
            else:
                # No conflict
                if self.decisionLevel()==0:
                    assert self.simplifyDB() # Cannot return false here
                if len(self.learnts)-self.nAssigns() >= nof_learnts:
                    # Reduce set of learnt clauses
                    self.reduceDB()
                if (self.nAssigns() == self.nVars()):
                    #print 'Model found'
                    # Model found
                    self.model = [v==LitTrue for v in self.assigns]
                    self.cancelUntil(self.root_level)
                    return LitTrue
                elif conflictC >= nof_conflicts:
                    # Reached bound on number of conflicts
                    self.cancelUntil(self.root_level)
                    return LitUndefined
                else:
                    # New variable decision
                    litp = lit(self.order.select()) # How to choose literal sense?
                    #print 'assigning',litp
                    assert self.assume(litp) # Cannot return false

    def varBumpActivity(self,v):
        self.activity[v] += self.var_inc
        if self.activity[v]>1e100:
            self.varRescaleActivity()
        self.order.update(v)

    def varDecayActivity(self):
        self.var_inc *= self.var_decay

    def varRescaleActivity(self):
        self.activity = [a*1e-100 for a in self.activity]
        self.var_inc *= 1e-100
        self.order.updateAll()

    def claBumpActivity(self,c):
        c.activity += self.cla_inc
        if c.activity>1e100:
            self.claRescaleActivity()

    def varDecayActivity(self):
        self.cla_inc *= self.cla_decay

    def claRescaleActivity(self):
        assert False

    def claDecayActivity(self):
        self.cla_inc *= self.cla_decay

    def decayActivities(self):
        self.varDecayActivity()
        self.claDecayActivity()

    def reduceDB(self):
        lim = self.cla_inc / (1+len(self.learnts))
        self.learnts.sort(key=lambda c:c.activity)
        t= len(self.learnts)
        self.learnts = [c for i,c in enumerate(self.learnts) if
                            not c.locked(self)
                            and (i<t or c.activity<lim)]

    def simplifyDB(self):
        """Return False if contradiction detected"""
        self.have_called_simplify = True
        if self.propagate():
            self.contradiction_found = True
            return False
        self.learnts = [c for c in self.learnts if not c.simplify(self)]
        self.constrs = [c for c in self.constrs if not c.simplify(self)]
        return True

    def solve(self,assumps=None):
        """Try to solve with restarts"""
        assert self.have_called_simplify
        if self.contradiction_found:
            return False

        if not assumps:
            assumps=[]

        nof_conflicts = 100
        nof_learnts = self. nConstraints()/3
        status = LitUndefined

        # Push incremental assumptions
        for a in assumps:
            if not self.assume(a) or self.propagate():
                self.cancelUntil(0)
                return False
        self.root_level = self.decisionLevel()

        # Solve
        while status==LitUndefined:
            print 'Search with ',nof_conflicts,
            status = self.search(nof_conflicts,nof_learnts)
            nof_conflicts *= 1.5
            nof_learnts *= 1.1

        self.cancelUntil(0)
        return status == LitTrue
    

def make_clause(S,ps,learnt):
    """Constructs a new clause based on array of literals in ps.

    learnt clauses are ones discovered by the model.
        All literals will be false except first.
        
    Returns False,None if model is inconsistent
    Returns False,out_clause if model is still consistent

    out_clause can be None if already satisfied.
    """
    if not learnt:
        # Normalize clause
        W=set(p for p in ps if S.value_lit(p)!=LitFalse) # Remove False literals
        for p in W: # Remove duplicates and true clauses
            if S.value_lit(p)==LitTrue:
                #print 'Always true clause',p,S.assigns[var(p)],S.value_lit(p)
                return True,None
            if p^1 in W:
                #print 'Contains p and not p'
                return True,None
        ps=list(W)
    if len(ps)==0:
        return False,None
    if len(ps)==1:
        return S.enqueue(ps[0]),None
    c = Clause(ps,learnt)
    if learnt:
        # Pick a second literal to watch
        # max_i is index of literal with highest decision level (not including 0)
        max_i = max(range(1,len(ps)),key=lambda i:S.level[var(ps[i])])
        ps[1],ps[max_i]=ps[max_i],ps[1]
        S.claBumpActivity(c) # Newly learnt clauses considered active
        for lit in ps:
            S.varBumpActivity(var(lit)) # Variables in conflict clauses are bumped   
    S.watches[ps[0]^1].append(c)
    S.watches[ps[1]^1].append(c)
    return True, c

    
class Clause(object):
    # Each clause watches the first two literals

    # For learnt clauses, all literals will be false except lits[0]

    def __init__(self,lits,learnt):
        self.learnt = learnt
        self.activity = 0.0
        self.lits = lits

    def locked(self,S):
        return S.reason[var(self.lits[0])] == self

    def remove(self,S):
        self.removeElem(S.watches[index(self.lits[0]^1)])
        self.removeElem(S.watches[index(self.lits[1]^1)])

    def simplify(self,S):
        """Simplify this constraint - False vars can be ignored, True vars can remove whole clause.

        Returns true if whole clause can be ignored."""
        j = 0
        L=self.lits
        for lit in L:
            v = S.value_lit(lit)
            if v == LitTrue:
                return True
            elif v == LitUndefined:  
                L[j] = lit
                j += 1
        self.lits = L[:j]
        return False

    def propagate(self,S,litp):
        """Propagate the setting of literal p.

        Ask this constraint whether more unit info can be inferred.
        If so, it is added to the queue"""
        # Make sure false literal is lits[1]
        A=S.assigns
        L=self.lits
        if L[0] == litp^1:
            L[0] = L[1]
            L[1] = litp^1
        # If watch is true, clause is satisfied
        #if S.value_lit(L[0])==LitTrue:
        if A[L[0]>>1] == 1-2*(L[0]&1):
            S.watches[litp].append(self)
            return True

        # Look for a new literal to watch
        i=2
        while i<len(L):
            #if S.value_lit(L[i]) != LitFalse:
            l=L[i]
            f=-1+2*(l&1)
            if A[l>>1] != f:
                L[1] = L[i]
                L[i] = litp^1
                S.watches[L[1]^1].append(self)
                return True
            i+=1

        # Clause is unit under assignment
        S.watches[litp].append(self)
        return S.enqueue(L[0],self)  # Enqueue for more propagation

    def calcReason(self,S,litp):
        """Returns vector of literals representing reason for inconsistency"""
        # Invariant, litp==LitUndefined or p==lits[0]
        start = 0 if (litp==LitUndefined) else 1
        if self.learnt:
            S.claBumpActivity(self)
        return [lit^1 for lit in self.lits[start:]]


def load_dimacs(fname):
    """Generate a solver from a DIMACS filename"""
    S=Solver()
    def f(x):
        # TODO use dictionary to map instead
        x=int(x)
        while abs(x) >= S.nVars():
            S.newVar()
        if x>0:
            return lit(x)
        else:
            return lit(-x)^1
 
    with open(fname) as fd:
        for line in fd:
            if line[0]=='c':
                continue
            if line[0]=='p':
                continue
            A=line.split()
            assert A[-1]=='0'
            S.addClause([f(a) for a in A[:-1]])
    return S
   
    

def test_aim():
    """Runs throught the AIM DIMACS examples and checks correctness"""
    dirname = "aim"
    for fname in os.listdir(dirname):
        if 'cnf' in fname:
            print fname,
            S=load_dimacs(os.path.join(dirname,fname))
            print "Solving",
            S.simplifyDB()
            v = S.solve()
            print v
            assert v==('yes' in fname)

t0=time.time()
#cProfile.run("test_aim()")
test_aim()
print time.time()-t0

# 8 seconds with cProfile
