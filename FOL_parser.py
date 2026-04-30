import re
import AST

class FOLParser:
    def __init__(self, text):
        # Remove all whitespace for easier parsing
        clean_text = text.replace(' ', '').replace('\n', '').replace('\r', '')
        
        # Tokenizer: splits the string and put all valid tokens into a list
        token_pattern = r'∀|∃|→|∧|∨|¬|\(|\)|\.|,|[\w]+'
        self.tokens = re.findall(token_pattern, clean_text)
        self.pos = 0

    def peek(self):
        """Looks at the current token without consuming it."""
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self, expected=None):
        """Consumes the current token and advances the position."""
        token = self.peek()
        if expected and token != expected:
            raise SyntaxError(f"Expected '{expected}', got '{token}' at position {self.pos}")
        self.pos += 1
        return token

    def parse(self):
        """Starts parsing and ensures the entire string is consumed."""
        formula = self.parse_formula()
        if self.peek() is not None:
            raise SyntaxError(f"Unexpected trailing tokens: {self.tokens[self.pos:]}")
        return formula
    def parse_term(self):
        """Recursively parses a term (variable, constant, or nested function like f(X))."""
        name = self.consume()
        # If the name is followed by '(', it's a function term
        if self.peek() == '(':
            self.consume('(')
            args = []
            while self.peek() != ')':
                args.append(self.parse_term())
                if self.peek() == ',':
                    self.consume(',')
            self.consume(')')
            # Reconstruct the nested function as a single string
            return f"{name}({', '.join(args)})"
        return name

    def parse_formula(self):
        """Recursively parses tokens into AST Formula objects."""
        token = self.peek()

        if token == '∀':
            self.consume('∀')
            var = self.consume()  # The variable name (e.g., 'x')
            self.consume('.')
            inner = self.parse_formula()
            return AST.ForAll(var, inner)

        elif token == '∃':
            self.consume('∃')
            var = self.consume()
            self.consume('.')
            inner = self.parse_formula()
            return AST.Exists(var, inner)

        elif token == '¬':
            self.consume('¬')
            # Handle optional parentheses around negations: ¬(A) vs ¬A
            has_paren = False
            if self.peek() == '(':
                self.consume('(')
                has_paren = True
                
            inner = self.parse_formula()
            
            if has_paren:
                self.consume(')')
            return AST.Not(inner)

        elif token == '(':
            self.consume('(')
            
            # 1. Parse the first formula inside the parentheses
            current_formula = self.parse_formula()

            # 2. Keep parsing as long as we see operators (handles A ∧ B ∧ C)
            while self.peek() in ['∧', '∨', '→']:
                op = self.consume()
                next_formula = self.parse_formula()
                
                if op == '∧': 
                    current_formula = AST.And(current_formula, next_formula)
                elif op == '∨': 
                    current_formula = AST.Or(current_formula, next_formula)
                elif op == '→': 
                    current_formula = AST.Implies(current_formula, next_formula)

            # 3. Finally, consume the closing parenthesis
            self.consume(')')
            
            # Returns the fully chained AST tree!
            return current_formula

        elif re.match(r'^[\w]+$', token): 
            # It's an identifier (Predicate name)
            name = self.consume()
            args = []
            
            # Check if the predicate has arguments: P(x, y)
            if self.peek() == '(':
                self.consume('(')
                while self.peek() != ')':
                    # FIX: Use parse_term() instead of consume() to handle functions!
                    args.append(self.parse_term())
                    if self.peek() == ',':
                        self.consume(',') # skip commas
                self.consume(')')
                
            return AST.Predicate(name, args)

        elif token in ['⊤', '⊥']:
            self.consume()
            if token == '⊤': return AST.Top()
            if token == '⊥': return AST.Bot()

        raise SyntaxError(f"Unexpected token '{token}' at index {self.pos}")
