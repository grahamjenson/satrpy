from rheapq import heappush
from rheapq import heappop
from rheapq import heapreplace

def main(argv):
  h = []
  a = [3, 'write spec']
  heappush(h, [1, 'write code'])
  heappush(h, [2, 'release product'])
  heappush(h, a)
  heappush(h, [4, 'create tests'])
  
  a[0] = 1
  print h
  print 'tt', heappop(h)
  print h
  print 'tt', heappop(h)
  print h
  print 'tt', heappop(h)
  print h

  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)