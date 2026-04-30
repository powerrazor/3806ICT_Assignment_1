import re

def get_constants_from_ast(node):
    """Recursively finds all 0-arity constant terms used in a formula."""
    if isinstance(node, Predicate):
        consts = set()
        for arg in node.args:
            matches = re.findall(r'\b([a-z][\w]*)\b(?!\()', arg)
            consts.update(matches)
        return consts
        
    elif isinstance(node, Not):
        return get_constants_from_ast(node.inner)
    elif isinstance(node, (And, Or, Implies)):
        return get_constants_from_ast(node.left) | get_constants_from_ast(node.right)
    elif isinstance(node, (ForAll, Exists)):
        consts = get_constants_from_ast(node.inner)
        consts.discard(node.var)
        return consts
    return set()

class Formula:
    """Base class for all logic formulas."""
    def is_top(self): return False
    def is_bot(self): return False
    def is_predicate(self): return False
    def is_not(self): return False
    def is_and(self): return False
    def is_or(self): return False
    def is_implies(self): return False
    def is_forall(self): return False
    def is_exists(self): return False

    def replace(self, var, term):
        """Recursively replaces free instances of 'var' with 'term'."""
        raise NotImplementedError

    def __eq__(self, other):
        raise NotImplementedError

# --- Constants & Predicates ---

class Top(Formula):
    def is_top(self): return True
    def replace(self, var, term): return self
    def __eq__(self, other): return isinstance(other, Top)
    def __str__(self): return "⊤"
    def __hash__(self): return hash("Top")

class Bot(Formula):
    def is_bot(self): return True
    def replace(self, var, term): return self
    def __eq__(self, other): return isinstance(other, Bot)
    def __str__(self): return "⊥"
    def __hash__(self): return hash("Bot")

class Predicate(Formula):
    def __init__(self, name, args):
        self.name = name
        self.args = args  # List of string variables/terms

    def is_predicate(self): return True
    
    def replace(self, var, term):
        import re # Ensure regex is imported
        new_args = []
        for arg in self.args:
            # Use regex word boundaries (\b) to replace the variable INSIDE nested functions
            # e.g., safely replaces 'Y' in 'f(Y)' with 'c' -> 'f(c)'
            new_arg = re.sub(r'\b' + re.escape(var) + r'\b', term, arg)
            new_args.append(new_arg)
        return type(self)(self.name, new_args)

    def __eq__(self, other):
        return isinstance(other, Predicate) and self.name == other.name and self.args == other.args

    def __str__(self):
        if not self.args: return self.name
        return f"{self.name}({', '.join(self.args)})"
    def __hash__(self): return hash((self.name, tuple(self.args)))

# --- Propositional Connectives ---

class Not(Formula):
    def __init__(self, inner):
        self.inner = inner
        
    def is_not(self): return True
    def replace(self, var, term): return Not(self.inner.replace(var, term))
    def __eq__(self, other): return isinstance(other, Not) and self.inner == other.inner
    def __str__(self): return f"¬({self.inner})"
    def __hash__(self): return hash(("Not", self.inner))

class And(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        
    def is_and(self): return True
    def replace(self, var, term): return And(self.left.replace(var, term), self.right.replace(var, term))
    def __eq__(self, other): return isinstance(other, And) and self.left == other.left and self.right == other.right
    def __str__(self): return f"({self.left} ∧ {self.right})"
    def __hash__(self): return hash(("And", self.left, self.right))

class Or(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        
        
    def is_or(self): return True
    def replace(self, var, term): return Or(self.left.replace(var, term), self.right.replace(var, term))
    def __eq__(self, other): return isinstance(other, Or) and self.left == other.left and self.right == other.right
    def __str__(self): return f"({self.left} ∨ {self.right})"
    def __hash__(self): return hash(("Or", self.left, self.right))

class Implies(Formula):
    def __init__(self, left, right):
        self.left = left
        self.right = right
        
    def is_implies(self): return True
    def replace(self, var, term): return Implies(self.left.replace(var, term), self.right.replace(var, term))
    def __eq__(self, other): return isinstance(other, Implies) and self.left == other.left and self.right == other.right
    def __str__(self): return f"({self.left} → {self.right})"
    def __hash__(self): return hash(("Implies", self.left, self.right))

# --- Quantifiers ---

class ForAll(Formula):
    def __init__(self, var, inner):
        self.var = var
        self.inner = inner
        
    def is_forall(self): return True
    
    def substitute(self, term):
        """Used by the prover to instantiate the bound variable."""
        return self.inner.replace(self.var, term)
        
    def replace(self, var, term):
        if self.var == var:
            return self  # Variable shadowing: don't replace inside a new scope
        return ForAll(self.var, self.inner.replace(var, term))
        
    def __eq__(self, other): 
        return isinstance(other, ForAll) and self.var == other.var and self.inner == other.inner
        
    def __str__(self): return f"∀{self.var}.{self.inner}"
    def __hash__(self): return hash(("ForAll", self.var, self.inner))

class Exists(Formula):
    def __init__(self, var, inner):
        self.var = var
        self.inner = inner
        
    def is_exists(self): return True
    
    def substitute(self, term):
        """Used by the prover to instantiate the bound variable."""
        return self.inner.replace(self.var, term)
        
    def replace(self, var, term):
        if self.var == var:
            return self  # Variable shadowing
        return Exists(self.var, self.inner.replace(var, term))
        
    def __eq__(self, other): 
        return isinstance(other, Exists) and self.var == other.var and self.inner == other.inner
        
    def __str__(self): return f"∃{self.var}.{self.inner}"

    def __hash__(self): return hash(("Exists", self.var, self.inner))