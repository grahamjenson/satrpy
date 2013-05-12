from solver import Variable
from solver import Formula
from solver import Clause

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
