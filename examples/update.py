#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jul 26 09:41:17 2024

@author: txa
"""

def update(d,key,val) :
    d=d.copy()
    d[key]=val
    return d
