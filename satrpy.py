from dimacs_parser import parse_to_formula
from solver import Solver

def main(argv):
  inputfile = argv[1]
  formula = parse_to_formula(inputfile)
  solver = Solver(formula)
  trail = solver.dpll()
  if trail is not None:
    print trail.__str__()
    print 'SATISFIABLE'
  else:
    print 'UNSATISFIABLE'
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)