from dimacs_parser import parse_to_formula
from solver import Solver

def main(argv):
  inputfile = argv[1]
  formula = parse_to_formula(inputfile)
  print formula.__str__()
  solver = Solver(formula)
  trail = solver.dpll()

  print trail.__str__()
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)