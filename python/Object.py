

class Object :
    
    # myClass : Object
    def mkClass(name,supper,inits,methods) :
        # Name is only for debugging
        return Instance(MetaClass(),{"name":name,"super":supper,"inits":inits,"methods":methods})
      
    def objectClass() :
        return Instance(MetaClass(),{})
  

class MetaClass (Object) :
    
    def __init__(self) :
        self.myclass = self
        
    # def __repr__(self) :
    #     return "MetaClass()"

    def __repr__(self) :
        return "Class"

class Instance (Object) :
      
    def __init__(self,myclass,state) :
        # myclass : Object
        # state : Dict (String , Object)
        self.myclass = myclass
        self.state = state
        
    def __eq__(self,other) : # we don't check class membership of other!
        return (self.myclass == other.myclass and self.state == other.state)
    
    def equal(self,other,env) :
        if self.myclass != other.myclass :
            return False
        ivars = self.state.keys()
        if ivars != other.state.keys() :
            return False
        for x in ivars :
            if not self.state[x].equal(other.state[x],env) :
                return False
        return True   

    def apply(self,objs,env) :
        # self.class = MetaClass (assertion)
        return Instance(self,dict(zip(self.state["inits"].params,objs)))
        
    def __repr__(self) :
        return f"Instance(myclass={self.myclass},state={self.state})"

    def __repr1__(self):
        # Description of class name and function names
        name = self.state.get("name", "???")
        ms   = self.state.get("methods", {}).items()
        methods = ", ".join([ name+str(method) for (name,method) in ms])
        # print(self.state)
        # super_name = self.state.get("super","")
        # return f"{name}:({super_name})[{methods}]"
        return f"{name}[{methods}]"