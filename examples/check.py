#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
@author: andorp
"""

def check(v,t:type) :
  if isinstance(v,t):
    return v
  else:
    raise TypeError(f"ERROR {t}")
