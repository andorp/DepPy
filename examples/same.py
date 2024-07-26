#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

# A 'proof' that two things are related computationally
#
# TODO: Refine this concept. I call it 'same' as this should be
# really an itchy spot. :) We will make this more price soon.
class Same :

  def __init__(self,v1,v2):
    self.v1 = v1
    self.v2 = v2

def same(v1,v2) :
  if v1.__same__(v2):
    return Same(v1,v2)
  else:
    raise TypeError(f"Not the same {v1} {v2}")

