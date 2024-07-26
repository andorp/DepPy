class Closure :
    def __init__(self,method,myself) :
        self.method = method
        self.myself = myself
        
    def apply(self,objs,env) :
        # objs : List Object
        localenv = env.copy()
        localenv.update(dict(zip(self.method.params,[self.myself]+list(objs))))
        return self.method.ret.eval(localenv)

class Expr :
    # eval (self, env : Dict (String , Object))
    # equal(self , other : Expr, env : Env)

    def equal(self,other,env) :
         return self.eval(env).equal(other.eval(env),env)
        
# class Constraint (Expr) :
#     def __init__(self,var,e) :
#         # name : String
#         # e    : Expr
#         self.var = var
#         self.e   = e

#     def eval(self,env) :
#         return self

#     def __repr__(self) :
#         return f"Constraint({self.name},{self.e})"

class Var (Expr) :
    def __init__(self,name) :
        # name : String
        self.name = name

    def eval(self,env) :
        return self
    
    def equal(self,other,env) :
        return self == other    

    def __repr__(self) :
        return f"Var({self.name})"
    
class Id (Expr) :
    def __init__(self,name) :
        # name : String
        self.name = name

    def eval(self,env) :
        return env[self.name]
        
    def __repr1__(self) :
        return f"Id({self.name})"

    def __repr__(self):
        return self.name

class Dot (Expr) :
    def __init__(self,e,f) :
        # e : Expr
        # f : String
        self.e = e
        self.f = f

    def eval(self, env) :
        # lookup in object
        obj = self.e.eval(env)
        try :
          return obj.state[self.f]
        except KeyError : 
            theclass = obj.myclass
            while True :
             try : 
                return Closure(theclass.state["methods"][self.f],obj)
             except KeyError :
                theclass = theclass.state["super"] 
        except AttributeError :
            return self
            
    def __repr1__(self) :
        return f"Dot({self.e},{self.f})"

    def __repr__(self):
        return f"{self.e}.{self.f}"

class Apply(Expr) :
    def __init__(self,e,args) :
        # e : Expr
        # args : List Expr
        self.e = e
        self.args = args

    def eval(self,env) :
        try :
            return self.e.eval(env).apply(map(lambda x:x.eval(env),self.args),env)   
        except AttributeError :
            return self

    def __repr1__(self) :
        return f"Apply({self.e},{self.args})"

    def __repr__(self):
        arguments = ", ".join([ str(a) for a in self.args ])
        return f"{self.e}({arguments})"

class Init :
    def __init__(self,constraints,params) :
        # constraints : List(Constraint)
        # params      : List(String)
        self.params      = params
        self.constraints = constraints
        
    def __repr1__(self) :
        return f"Init({self.constraints},{self.params})"

    def __repr__(self) :
        return f"({self.constraints},{self.params})"

class Method : 
    def __init__(self,params,ret) :
        # params : List String
        # body : Expr
        self.params = params
        self.ret = ret
        
    def apply(self,objs,env) :
        # objs : List Object
        localenv = env.copy()
        localenv.update(dict(zip(self.params,objs)))
        return self.ret.eval(localenv)
    
    def __repr1__(self) :
        return f"Method({self.params},{self.ret})"

    def __repr__(self):
        parameters = ', '.join(self.params)
        return f"({parameters}) => {self.ret}"