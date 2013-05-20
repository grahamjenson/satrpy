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
    print 'u', self.__str__()
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
        print 'l', w.__str__()
        return w
    return None

  def __str__(self):
    prefix = ""
    if not self.pos:
      prefix = "-"
    tmp = prefix + str(self.var.name)
    if self.reason:
      tmp += '[r]'
    if self.is_falsified():
      tmp += '[-]'
    elif self.is_satisfied():
      tmp +='[+]'
    else:
      tmp += '[?]'
    return tmp 


######################Contraints
class Constraint:
  def __str__(self):
    tmp = "["
    delim = ''
    for lit in self.lits:
      tmp+= delim + lit.__str__()      
      delim = ' ,'
    tmp += "]"
    return tmp

  def is_unit_clause(self):
    return False

class UnitClause(Constraint):
  def __init__(self,lits):
    assert len(lits) == 1
    self.lits = lits
    self.lits[0].neg.add_watch(self)
    raise "asd"

  def propagate(self, trail, p):
    assert p.neg == self.lits[0]
    return trail.enqueue(self.lits[0], self)
  
  def is_unit_clause(self):
    return True
  

class Clause(Constraint):
  def __init__(self,lits):
    #sort lits to make free lits at the front
    nlits = []
    for l in lits:
      if l.is_free():
        nlits = [l] + nlits
      else:
        nlits = nlits + [l]

    self.lits = nlits
    #clause [1,2,3,4]
    #watch -1 and -2, if they get assigned we
    #move -1 to the beack and watch

    #should be unit
    if self.lits[0].is_falsified():
      #print map(lambda x: x.is_free(), self.lits)
      assert False

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

    assert self.lits[1].is_falsified();
    # the clause is now either unit or null
    if not (self.is_unit() or self.is_null()):
      print 'not null or unit', self.__str__()
      assert False

    p.add_watch(self)
    return trail.enqueue(self.lits[0],self)

  def is_unit(self):
    free = 0
    for l in self.lits:
      if l.is_free() or l.is_satisfied():
        free += 1
    return free == 1

  def is_null(self):
    for l in self.lits:
      if not l.is_falsified():
        return False
    return True
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
      print 'e falsified',p.__str__()
      return False
    elif p.is_satisfied():
      return True
    else:
      self._head.append(p)
      p.reason = constr
      p.assign()
      return True

  def add_to_order(self,p):
    p.inc_heur()
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
    #for name, v in self.formula.variables.items():
    for name in [24, 25, 26, 27, 20, 21, 22, 23, 28, 29, 4, 8, 59, 58, 55, 54, 57, 56, 51, 50, 53, 52, 88, 89, 82, 83, 80, 81, 86, 87, 84, 85, 3, 7, 100, 39, 38, 33, 32, 31, 30, 37, 36, 35, 34, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 2, 6, 99, 98, 91, 90, 93, 92, 95, 94, 97, 96, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 48, 49, 46, 47, 44, 45, 42, 43, 40, 41, 1, 5, 9, 77, 76, 75, 74, 73, 72, 71, 70, 79, 78]:
      v = self.formula.variables[name.__str__()]
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
    print 'analyze', confl.__str__()
    assert confl.is_null() or confl.is_unit()
    p, reason = self.trail.pop_trail()
    nlits = self.simple_resolution(confl.lits, reason.lits)
    print map(str,nlits)

    while not self.has_free_literal(nlits):
      if reason:
        ls = reason.lits
      else:
        ls = []
      if self.trail.size() != 0:
        p, reason = self.trail.pop_trail()
      else:
        print 'ran out', confl.__str__(), reason.__str__(), p.neg.__str__(), self.trail.__str__()
        return None

    
    
    c = create_constr(nlits)
    #print 't', self.trail.__str__()
    # #print 'p', p.neg.__str__()
    # while not self.has_free_literal(nlits):
    #   #print 'c', map(str, nlits)
    #   print 't', self.trail.__str__() 
    #   #print map(lambda x: x.is_free(), nlits)
    #   p, reason = self.trail.pop_trail()
    
    c = self.create_constr(nlits)
    if c is None:
      print 'failed', self.trail
      return None

    self.learnt.append(c)

    self.trail.enqueue(p.neg, confl)

    return confl


  def has_falsidied_literal(self,lits):
    for l in lits:
      if l.is_falsified():
        return True
    return False

  def has_free_literal(self,lits):
    for l in lits:
      if l.is_free():
        return True
    return False

  def create_constr(self, lits):
    l = len(lits)
    if l == 0:
      print 'conflict'
      return None
    elif l == 1:
      print 'unit'
      return UnitClause(lits)
    else:
      return Clause(lits)

  def simple_resolution(self,lits1,lits2):
    nlits = []
    neg = False
    for l in lits1:
      if l in nlits:
        continue
      if l.neg in lits2:
        neg = True
      else:
        nlits.append(l)
    
    if not neg:
      assert False

    for l in lits2:
      if l in nlits:
        continue
      if l.neg in lits1:
        neg = True
      else:
        nlits.append(l)

    return nlits

  def propagate(self):
    #while there are still un propagated lits
    while self.trail.head_length() > 0:
      p = self.trail.inc_head()
      confl = p.propagate(self.trail)
      if confl is not None: # propagate lit and return conflict if it breaks
        #the propagation didnt work
        return confl
    return None
