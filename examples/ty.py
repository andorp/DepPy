
class Ty:
  pass

class TyType (Ty):
  def __init__(self,tc:type):
    self.tc = tc

class TyVal (Ty):
  def __init__(self,x):
    self.x = x

class TyVar (Ty):
  def __init__(self,n:str):
    self.n = n

class TyAutoVar (Ty):
  index = 0
  def __init__(self,n:str):
    self.n = n
    self.i = TyAutoVar.index
    TyAutoVar.index = TyAutoVar.index + 1

class Unification:

  constraints = []

  def unify(cls,t:Ty,r:Ty) -> Ty:
    u = TyAutoVar("u")
    Unification.constraints.add(u,t)
    Unification.constraints.add(u,r)
    Unification.constraints.add(t,r)
    return u
