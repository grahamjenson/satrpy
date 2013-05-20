from rheapq import heappush
from rheapq import heappop
from rheapq import heapreplace
from solver import *

def main(argv):
  s = Solver(Formula([],{}))
  
  v1 = Variable('1')
  v2 = Variable('2')
  v3 = Variable('3')
  v4 = Variable('4')
  v5 = Variable('5')
  v6 = Variable('6')

  c1 = [v1.pos,v2.pos,v3.pos]
  c2 = [v1.neg, v2.pos, v5.pos]

  print map(lambda x: str(x), c1)
  print map(lambda x: str(x), c2)

  a = s.simple_resolution(c1,c2)

  print map(lambda x: str(x), a)
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)