from rheapq import heappush
from rheapq import heappop
from rheapq import heapreplace
from rqueue import PriorityQueue 
def main(argv):
  que = PriorityQueue(100)
  que.put(1)
  print que.get()
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)