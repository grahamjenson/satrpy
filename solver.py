###########Utils
class Utils:
  @staticmethod
  def has_duplicate_lits(nlits):
    lits = []
    for l in nlits:
      if l in lits:
        return True
      else:
        lits.append(l)
    return False

  @staticmethod
  def is_tautology(nlits):
    for l in nlits:
      if l.neg in nlits:
        return True
    return False

  @staticmethod
  def is_unit(nlits):
    free = 0
    for l in nlits:
      if l.is_free() or l.is_satisfied():
        free += 1
      if free == 2:
        return False
    return free == 1

  @staticmethod
  def is_null(nlits):
    for l in nlits:
      if not l.is_falsified():
        return False
    return True

  @staticmethod
  def has_free_lit(nlits):
    for l in nlits:
      if l.is_free():
        return True
    return False

  @staticmethod
  def get_unit_lit(nlits):
    assert Utils.is_unit(nlits)
    return Utils.get_free_lit(nlits)

  @staticmethod
  def get_free_lit(nlits):
    assert Utils.has_free_lit(nlits)
    for l in nlits:
      if l.is_free():
        return l
    assert False

#################VARIABELES
class Variable:
  def __init__(self,name):
    self.pos = Literal(self, True)
    self.neg = Literal(self, False)
    self.neg.neg = self.pos
    self.pos.neg = self.neg
    self.name = name

class Literal:
  def __init__(self, var, pos):
    self.var = var
    self.pos = pos
    self.reason = None
    self.assigned = False
    self.watches = []
    self.h = 0
    self.decision_level = -1

  def heur(self):
    return self.h

  def reset_heur(self):
    self.h = -1

  def dec_heur(self):
    self.h -= 1

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
    tmp = prefix + str(self.var.name)
    if self.reason:
      if self.reason.is_unit_clause():
        tmp += '[U]'
      else:
        tmp += '[r]'
    if self.is_falsified():
      tmp += '[-]'
    elif self.is_satisfied():
      tmp +='[+'+ str(self.decision_level) +']'
    else:
      tmp += '[?]'
    return tmp 

######################Contraints
class Constraint:
  def __init__(self):
    self.learnt = False

  def __str__(self):
    tmp = "["
    delim = ''
    for lit in self.lits:
      tmp+= delim + lit.__str__()      
      delim = ' ,'
    tmp += "]"
    if self.learnt:
      tmp += '[L]'
    return tmp

  def is_unit_clause(self):
    return False
  
  def is_unit(self):
    return Utils.is_unit(self.lits)

  def is_null(self):
    return Utils.is_null(self.lits)

  def get_unit_lit(self):
    return Utils.get_unit_lit(self.lits)

  def get_free_lit(self):
    return Utils.get_free_lit(self.lits)

class UnitClause(Constraint):
  def __init__(self,lits):
    assert len(lits) == 1
    Constraint.__init__(self)
    self.lits = lits
    self.lits[0].neg.add_watch(self)

  def propagate(self, trail, p):
    assert False # should always be true so never be propogated

  def is_unit_clause(self):
    return True
  
class Clause(Constraint):
  def __init__(self,lits):
    Constraint.__init__(self)
    nlits = []
    for l in lits:
      if l.is_free():
        nlits = [l] + nlits
      else:
        nlits = nlits + [l]
    self.lits = nlits
    #should be unit
    assert not self.lits[0].is_falsified()

    self.lits[0].neg.add_watch(self)
    self.lits[1].neg.add_watch(self)

  def propagate(self, trail, p):
    #make the lit one false, that way lit[0] will always be unit
    # so if -1 == p, then list will be [2,1,3,4] 
    if self.lits[0] == p.neg:
      self.lits[0] = self.lits[1]
      self.lits[1] = p.neg

    # lits[1] must contain the falsified literal
    if self.lits[1] != p.neg:
      assert False

    # look for new literal to watch: no strategy
    for i, lit in enumerate(self.lits[2:]):
      i = i + 2 # manage the offset
      if not lit.is_falsified():
        self.lits[1] = self.lits[i]
        self.lits[i] = p.neg
        self.lits[1].neg.add_watch(self)
        return True; # not unit yet as 

    assert self.lits[1].is_falsified()
    assert (self.is_unit() or self.is_null())
    p.add_watch(self)
    return trail.enqueue(self.lits[0],self)

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


#######################TRAIL
from rheapq import heappush
from rheapq import heappop

class Trail:
  def __init__(self):
    self._lit_order = [] #maintain order of assignments
    self._head = []
    self._order = []
    self._level = 0

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
  def decision_level(self):
    return self._level

  def add_to_tail(self, p):
    self._lit_order.append(p)

  def size(self):
    return len(self._lit_order)

  def size_of_head(self):
    return len(self._head)

  def peek(self):
    return self._lit_order[-1]
  
  def peek_head(self):
    return self._head[-1]

  def pop_till_unit(self):
    while self.size() != 0:
      if self.peek().reason is not None:
        if self.peek().reason.is_unit_clause():
          return
      p,r = self.pop_trail()
      #p.reset_heur()

  def pop_till_decision(self):
    while self.size() != 0:
      p, reason = self.pop_trail()
      if reason is None:
        break
    return 

  def pop_trail(self):
    if self.peek().reason is not None:
      if self.peek().reason.is_unit_clause():
        ##print self.__str__()
        return None,None

    p = self._lit_order.pop()
    p.unassign()
    constr = p.reason
    p.reason = None
    if constr is None:
      self._level -= 1
    p.decision_level = -1

    return p, constr

  def clear_head(self):
    ##print 'clear head', self.__str__()
    for p in self._head:
      p.reason = None
      p.unassign()
      p.decision_level = -1
    self._head = []
    ##print 'after clear head', self.__str__()

  def inc_head(self):
    p = self._head.pop()
    self.add_to_tail(p)
    return p

  def enqueue(self,p,constr):
    ##print 'enqueue', p.__str__(), 'because', constr.__str__()
    if p is None:
      return True
    if p.is_falsified():
      return False
    elif p.is_satisfied():
      return True
    else:
      self._head.append(p)
      p.reason = constr

      if constr is None:
        self._level += 1
      else:
        assert constr.is_unit()

      p.decision_level = self._level
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
    self.learnt = []
    #tis breaking on cnfs/sat/aim-100-3_4-yes1-1.cnf but only with this order
    for name, v in self.formula.variables.items():
      v = self.formula.variables[name]
      self.trail.add_to_order(v.pos)
      self.trail.add_to_order(v.neg)

  def dpll(self):
    alit = self.trail.decide()
    self.trail.enqueue(alit,None)

    while self.trail.size_of_head() > 0:
      assert self.trail.size_of_head() == 1
      confl = self.propagate()
      if confl is not None:
        nlits = self.analyze(confl)
        if nlits is None:
          return None
        
        self.trail.clear_head()
        while not Utils.has_free_lit(nlits):
          if self.trail.decision_level() == 0:
            return None
          self.trail.pop_till_decision()

        nconfl = self.create_constr(nlits)
        self.learnt.append(nconfl)
        nconfl.learnt = True
        
        if nconfl.is_unit_clause() or len(self.learnt) % 100 == 0:
          self.trail.pop_till_unit()

        free_lit = nconfl.get_free_lit()
        if nconfl.is_unit():
          self.trail.enqueue(free_lit, nconfl)
        else:
          self.trail.enqueue(free_lit, None)

      else:
        alit = self.trail.decide()
        self.trail.enqueue(alit,None)
    
    return self.trail

  def analyze(self, confl):
    assert confl.is_null()

    nlits = [] + confl.lits
    max_level = self.max_decision_level(nlits)
    seen = []
    assert max_level >= self.trail.decision_level()

    while max_level >= self.trail.decision_level():
      pivot = self.find_pivot(nlits,max_level)
      assert pivot is not None

      if pivot in seen:
        break

      seen.append(pivot)
      seen.append(pivot.neg)
      if pivot.neg.reason is None:
        continue
      nlits = self.resolution(pivot, nlits, pivot.neg.reason.lits)
      max_level = self.max_decision_level(nlits)

    assert not Utils.has_duplicate_lits(nlits)
    #Create contraint
    return nlits

  def max_decision_level(self,lits):
    m = -1
    for l in lits:
      if l.neg.decision_level > m:
        m = l.neg.decision_level
    return m

  def create_constr(self, lits):
    l = len(lits)
    if l == 0:
      return None
    elif l == 1:
      return UnitClause(lits)
    else:
      return Clause(lits)

  def find_pivot(self,lits,level):
    for l in lits:
      if l.neg.decision_level == level:
        return l
    return None

  def resolution(self,pivot,lits1,lits2):
    nlits = []
    assert pivot is not None
    assert pivot in lits1
    assert pivot.neg in lits2

    for l in lits1 + lits2:
      if l in nlits:
        continue
      elif l is pivot or l.neg is pivot:
        continue
      else:
        nlits.append(l)
        l.inc_heur()
        l.neg.inc_heur()
    return nlits

  def propagate(self):
    #while there are still un propagated lits
    while self.trail.size_of_head() > 0:
      p = self.trail.inc_head()
      confl = p.propagate(self.trail)
      if confl is not None: # propagate lit and return conflict if it breaks
        #the propagation didnt work
        return confl
    return None
