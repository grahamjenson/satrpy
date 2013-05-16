#################VARIABELES

class Variable:
  def __init__(self,name):
    self.pos = Literal(self, True)
    self.neg = Literal(self, False)
    self.neg.neg = self.pos
    self.pos.neg = self.neg
    self.name = name

class Literal:
  def __init__(self,var, pos):
    self.var = var
    self.pos = pos
    self.reason = None
    self.assigned = False
    self.watches = []
    self.h = 0

  def heur(self):
    return self.h

  def inc_heur(self):
    self.h -= 1

  def assign(self):
    assert self.assigned == False
    assert self.neg.assigned == False
    self.assigned = True
  
  def unassign(self):
    assert self.assigned == True
    assert self.neg.assigned == False
    self.assigned = False

  def is_free(self):
    return self.assigned == False and self.neg.assigned == False

  def is_satisfied(self):
    return self.assigned == True and self.neg.assigned == False

  def is_falsified(self):
    return self.assigned == False and self.neg.assigned == True  

  def add_watch(self, confl):
    self.watches.append(confl)

  def remove_watch(self, confl):
    self.watches.remove(confl)

  def propagate(self, trail):
    tmp = self.watches
    self.watches = []
    while tmp:
      w = tmp.pop()
      if not w.propagate(trail,self):
        self.watches += tmp 
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

  def propagate(self, trail, p):
    #make the lit one false, that way lit[0] will always be unit
    # so if -1 == p, then list will be [2,1,3,4] 
    if self.lits[0] == p.neg:
      self.lits[0] = self.lits[1]
      self.lits[1] = p.neg

    # lits[1] must contain the falsified literal
    assert self.lits[1] == p.neg

    # look for new literal to watch: no strategy
    for i, lit in enumerate(self.lits[2:]):
      i = i + 2 # manage the offset
      if not lit.is_falsified():
        self.lits[1] = self.lits[i];
        self.lits[i] = p.neg;
        self.lits[1].neg.add_watch(self);
        return True; # not unit yet as 

    assert self.lits[1].is_falsified();
    # the clause is now either unit or null
    p.add_watch(self)
    return trail.enqueue(self.lits[0],self)
  

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
from rheapq import heappush
from rheapq import heappop

class Trail:
  def __init__(self):
    self._lit_order = [] #maintain order of assignments
    self._head = []
    self._order = []

  def __str__(self):
    tmp = "["
    delim = ''
    for l in self._lit_order:
      tmp += delim
      tmp += l.__str__()
      delim = ', '
    tmp += ']  ['
    
    delim = ''
    for l in self._head:
      tmp += delim
      tmp += l.__str__()
      delim = ', '
    tmp += ']'
    return tmp

  def add_to_tail(self, p):
    self._lit_order.append(p)

  def size(self):
    return len(self._lit_order)

  def pop_trail(self):
    p = self._lit_order.pop()
    p.unassign()
    constr = p.reason
    p.reason = None
    return p, constr

  def head_length(self):
    return len(self._head)
  
  def clear_head(self):
    for p in self._head:
      p.reason = None
      p.unassign()
    self._head = []

  def inc_head(self):
    p = self._head.pop()
    self.add_to_tail(p)
    return p

  def enqueue(self,p,constr):
    if p is None:
      return True
    
    if p.is_falsified():
      return False
    elif p.is_satisfied():
      return True
    else:
      self._head.append(p)
      p.reason = constr
      p.assign()
      return True

  def add_to_order(self,p):
    heappush(self._order, p)

  def decide(self):
    lits = []
    lit = heappop(self._order)
    lits.append(lit)
    while not lit.is_free():
      if len(self._order) == 0:
        return None
      lit = heappop(self._order)
      lits.append(lit)

    for l in lits:
      heappush(self._order, l)
      #add lits back

    return lit

#########################Solver
class Solver:
  
  def __init__(self,formula):
    self.trail = Trail()
    self.formula = formula
    for name, v in self.formula.variables.items():
      self.trail.add_to_order(v.pos)
      self.trail.add_to_order(v.neg)

  def dpll(self):
    alit = self.trail.decide()
    self.trail.enqueue(alit,None)

    while self.trail.head_length() > 0:
      assert self.trail.head_length() == 1
      confl = self.propagate()
      if confl is not None:
        self.trail.clear_head()
        if self.analyze(confl) is None:
          return None
      else:
        alit = self.trail.decide()
        self.trail.enqueue(alit,None)
    
    return self.trail

  def analyze(self, confl):
    #TODO backtrack till last decision
    #change decision, and give this conflict as the reason!
    p, reason = self.trail.pop_trail()
    while reason is not None:
      if self.trail.size() != 0:
        p, reason = self.trail.pop_trail()
      else:
        return None

    p.inc_heur()
    
    self.trail.enqueue(p.neg, confl)
    return confl

  def propagate(self):
    #while there are still un propagated lits
    while self.trail.head_length() > 0:
      p = self.trail.inc_head()
      confl = p.propagate(self.trail)
      if confl is not None: # propagate lit and return conflict if it breaks
        #the propagation didnt work
        return confl
    return None
