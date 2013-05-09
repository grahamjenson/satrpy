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


import os
def read_lines(inputfile):
  f = os.open(inputfile, os.O_RDONLY, 0777)
  x = os.read(f,1)
  lines = []
  tmpstr = ""
  while x != '':
    if x == '\n':
      lines.append(tmpstr)
      tmpstr = ""
    else:
      tmpstr += x
    x = os.read(f,1)
  
  lines.append(tmpstr)
  return lines


def parse_to_formula(inputfile):
  lines = read_lines(inputfile)
  print lines
  clauses = []
  variables = {}
  for rec in lines:
    rec = rec.strip(' ')
    if (rec[0] == 'c') or (rec[0] == 'p'):
      continue
    lits = []
    for num in rec.split(' '):
      num = num.strip(' ')
      if num != '0':
        lit = find_or_create_literal(num,variables)
        lits.append(lit)
    clauses.append(Clause(lits))
  return Formula(clauses,variables)

def main(argv):
  inputfile = argv[1]
  formula = parse_to_formula(inputfile)

  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)