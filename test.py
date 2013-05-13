import collections

def x(a):
  return 1, a.__str__()

def main(argv):
  print x(1)
  print x(None);
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)