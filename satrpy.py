#satrpy.py
test_data = [ "c The random seed used to shuffle this instance was seed=1755086696",
              "p cnf 1200 4919",
              "-35 491 -1180 0",
              "479 1074 -949 0",
              "609 1177 -67 0" ]


class Variable:
  def __init__(self,name):
    self.pos = Literal(self, True)
    self.neg = Literal(self, False)
    self.name = name

class Literal:
  def __init__(self,var, pos):
    self.var = var
    self.pos = pos

  def __str__(self):
    prefix = ""
    if not self.pos:
      prefix = "-"

    return prefix + str(self.var.name)

class Clause:
  def __init__(self,lits):
    self.lits = lits
  
  def __str__(self):
    tmp = "["
    delim = ''
    for lit in self.lits:
      tmp+= delim + lit.__str__()      
      delim = ' ,'
    tmp += "]"
    return tmp

class Formula:
  def __init__(self,clauses, variables):
    self.clauses = clauses
    self.variables = variables

def find_or_create_literal(num, variables):
  
  if num.startswith("-"):
    neg = True
    num = num[1:]
  else:
    neg = False
  
  if num in variables:
    var = variables[num]
  else:
    var = Variable(num)
    variables[num] = var

  if neg:
    return var.neg
  else:
    return var.pos


def parse_to_formula(inputfile):
  #f = open(inputfile)
  clauses = []
  variables = {}
  for rec in test_data:
     rec = rec.strip(' ')
     lits = []
     ## record has to start with a number or a minus sign
     if (rec[0].isdigit()) or (rec[0].startswith("-")):
        substrs = rec.split(' ')
        for num in substrs:
            num = num.strip(' ')
            if num != '0':
              lit = find_or_create_literal(num,variables)
              lits.append(lit)

        clauses.append(Clause(lits))
  return Formula(clauses,variables)

def main(argv):
  inputfile = argv[1]
  formula = parse_to_formula(inputfile)
  for c in formula.clauses:
    print c.__str__()
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)