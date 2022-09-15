#!/bin/env python3
import json
from sys import argv

def compare_rewrites(name1,name2,j1,j2):
      for rw in j1['rewrites']:
          found = False
          for rw_cmp in j2['rewrites']:
              if rw['lhs'] == rw_cmp['lhs'] and rw['rhs'] == rw_cmp['rhs']:
                  found = True
          if not found:
              print(f"{name1} has rw: {rw} which is not in {name2}")

with open(argv[1],'r') as f1:
  with open(argv[2],'r') as f2:
      j1 = json.load(f1)
      j2 = json.load(f2)
      compare_rewrites(argv[1],argv[2],j1,j2)
      compare_rewrites(argv[2],argv[1],j2,j1)
