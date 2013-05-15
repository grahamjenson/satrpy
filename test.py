#!/usr/bin/python
import os
import shutil
import sys
import argparse
import random 
import time,datetime
import subprocess


#initial system
#time, request, system, 
  
def main():
  satdir = './cnfs/sat'
  unsatdir = './cnfs/unsat'

  parser = argparse.ArgumentParser(prog="test solver", description='Test solver')
  parser.add_argument('-s',"--solver",  type=str, required=True)
  args = parser.parse_args()

  for cnffile in os.listdir(satdir):
    path = os.path.join(satdir,cnffile)
    print "executing sat", path
    process = subprocess.Popen(["./" + args.solver, path])
    out, err = process.communicate()
    print(out)
  
if __name__ == "__main__":
  main()


