import collections

def main(argv):
  d = collections.OrderedDict()
  d[1] = 'a'
  d[2] = 'b'
  print d
  return 0

def target(*args):
  return main, None

if __name__ == '__main__':
  import sys
  main(sys.argv)