from dimacs_parser import parse_to_formula
from solver import dpll
from solver import Solver

def main(argv):
  inputfile = argv[1]
  formula = parse_to_formula(inputfile)
  solver = Solver()
  solver.dpll(formula)

  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)