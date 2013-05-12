#################VARIABELES

class Variable:
  def __init__(self,name):
    self.pos = Literal(self, True)
    self.neg = Literal(self, False)
    self.name = name

class Literal:
  def __init__(self,var, pos):
    self.var = var
    self.pos = pos
    if self.pos:
      self.neg = self.var.neg
    else:
      self.neg = self.var.pos

    self.watches = []

  def add_watch(confl):
    self.watches.append(confl)

  def remove_watch(confl):
    self.watches.remove(confl)

  def propagate(trail):
    while self.watches:
      w = self.watches.pop()
      if not w.propagate(trail,self):
        return w
    return None

  def __str__(self):
    prefix = ""
    if not self.pos:
      prefix = "-"

    return prefix + str(self.var.name)


######################CLAUSES
class Clause:
  def __init__(self,lits):
    self.lits = lits
    #clause [1,2,3,4]
    #watch -1 and -2, if they get assigned we
    #move -1 to the beack and watch
    self.lits[0].neg.add_watch(self)
    self.lits[1].neg.add_watch(self)

  def propagate(trail, p):
    #make the lit one false, that way lit[0] will always be unit
    # so if -1 == p, then list will be [2,1,3,4] 
    if self.lits[0] == p.neg
      self.lits[0] = self.lits[1]
      self.lits[1] = p.neg

    # lits[1] must contain the falsified literal
    assert self.lits[1] == p.neg

    # look for new literal to watch: no strategy
    for i, lit in enumerate(self.lits[2:]):
      i = i + 2 # manage the offset
      if not trail.isFalsified(lit) {
        self.lits[1] = self.lits[i];
        self.lits[i] = p.neg;
        self.lits[1].neg.add_watch(self);
        return True; # not unit yet as 

    assert trail.isFalsified(self.lits[1]);
    # the clause is now either unit or null
    p.add_watch(self)
    return trail.enqueue(self.lits[0])

  def __str__(self):
    tmp = "["
    delim = ''
    for lit in self.lits:
      tmp+= delim + lit.__str__()      
      delim = ' ,'
    tmp += "]"
    return tmp


########################FORMULA
class Formula:
  def __init__(self,clauses, variables):
    self.clauses = clauses
    self.variables = variables

  def __str__(self):
    tmp = "["
    delim = ''
    for c in self.clauses:
      tmp+= delim + c.__str__()      
      delim = ' ,'
    tmp += "]"
    return tmp


#######################
class Trail:
  def __init__(self):
    self._vars = {} # fast lookup of assigned variables
    self._lit_order = [] #maintain order of assignments
    self._head = []

  def add_to_tail(self):
    self._vars[p.var] = p
    self._lit_order.append(p)

  def pop_trail(self):
    p = self._lit_order.pop()
    self._vars[p.var] = None
    return p

  def head_length(self):
    return len(self._head)
  
  def clear_head(self):
    self._head = []

  def pop_head(self):
    return self._head.pop()

  def lits(self):
    return self._vars.keys()

  def isFalsified(self,lit):
    return self._vars[lit.var] == lit.neg

  def isSatified(self, lit):
    return self._vars[lit.var] == lit

  def isFree(self, var):
    return var not in self._vars

  def enqueue(self,p):
    if self.isFalsified(p):
      return False
    else:
      self.add_to_tail(p)
      return True

  def assume(self, lit):
    return self._head.append(lit)

#########################Solver
class Solver
  
  def __init__(self,formula):
    self.trail = Trail()
    self.formula = formula

  def dpll(self):
    while self.trail.head_length() > 0:
      assert self.trail.head_length() == 1
      confl = propagate()
      if confl != None:
        self.trail.clear_head()
        self.analyze(confl)
      else:
        assumed = self.assume()
        self.trail.assume(v.pos)
    
  def analyze(confl):
    #TODO backtrack till last decision
    #change decision, and give this conflict as the reason!
    self.trail.pop_trail()
    confl

  def propagate():
    #while there are still un propagated lits
    while self.trail.head_length() > 0:
      p = self.trail.pop_head()  # get lit from top
      confl = p.propagate(self.trail)
      if confl != None: # propagate lit and return conflict if it breaks
        #the propagation didnt work
        analyze(confl)

    return None

  def choose():
    for v in self.formula.variables:
      if self.trail.isFree(v):
        return v.pos
    return None




