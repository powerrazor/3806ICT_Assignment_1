print("Welcome to this prover program. ")
from collections import deque
import itertools
import FOL_parser


class Sequent:
    def __init__(self, gamma, delta, used_insts=None, domain_terms=None):
        self.gamma = gamma
        self.delta = delta
        self.used_insts = used_insts if used_insts is not None else set()
        self.domain_terms = domain_terms if domain_terms is not None else ["c"]

    def is_axiom(self):
        for fL in self.gamma:
            for fR in self.delta:
                if str(fL) == str(fR): 
                    return True
        if any(f.is_top() for f in self.delta): return True
        if any(f.is_bot() for f in self.gamma): return True
        return False

def prove_lk_baseline(formula, initial_domain=None):
    init_domain = list(initial_domain) if initial_domain else ["c"]
    term_counter = itertools.count(1) 
    
    initial_sequent = Sequent(gamma=[], delta=[formula], used_insts=set(), domain_terms=init_domain)
    open_branches = deque([initial_sequent])
    
    while open_branches:
        seq = open_branches.popleft()
        
        if seq.is_axiom():
            continue 
            
        applied_rule = False

        # 2. Non-branching rules
        for i, f in enumerate(seq.gamma):
            if f.is_and():
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:] + [f.left, f.right]
                open_branches.append(Sequent(new_gamma, seq.delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_not():
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:]
                new_delta = seq.delta + [f.inner]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_exists(): # Exists L creates eigenvariable
                fresh_var = f"e_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                if fresh_var not in new_domain: new_domain.append(fresh_var)
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:] + [f.substitute(fresh_var)]
                open_branches.append(Sequent(new_gamma, seq.delta, set(seq.used_insts), new_domain))
                applied_rule = True; break
        if applied_rule: continue

        for i, f in enumerate(seq.delta):
            if f.is_or():
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.left, f.right]
                open_branches.append(Sequent(seq.gamma, new_delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_implies():
                new_gamma = seq.gamma + [f.left]
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.right]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_not():
                new_gamma = seq.gamma + [f.inner]
                new_delta = seq.delta[:i] + seq.delta[i+1:]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_forall(): # Forall R creates eigenvariable
                fresh_var = f"e_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                if fresh_var not in new_domain: new_domain.append(fresh_var)
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.substitute(fresh_var)]
                open_branches.append(Sequent(seq.gamma, new_delta, set(seq.used_insts), new_domain))
                applied_rule = True; break
        if applied_rule: continue

        # 3. Branching rules
        for i, f in enumerate(seq.gamma):
            if f.is_or():
                g_rem = seq.gamma[:i] + seq.gamma[i+1:]
                open_branches.append(Sequent(g_rem + [f.left], seq.delta, set(seq.used_insts), list(seq.domain_terms)))
                open_branches.append(Sequent(g_rem + [f.right], seq.delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
            elif f.is_implies():
                g_rem = seq.gamma[:i] + seq.gamma[i+1:]
                open_branches.append(Sequent(g_rem, seq.delta + [f.left], set(seq.used_insts), list(seq.domain_terms)))
                open_branches.append(Sequent(g_rem + [f.right], seq.delta, set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
        if applied_rule: continue

        for i, f in enumerate(seq.delta):
            if f.is_and():
                d_rem = seq.delta[:i] + seq.delta[i+1:]
                open_branches.append(Sequent(seq.gamma, d_rem + [f.left], set(seq.used_insts), list(seq.domain_terms)))
                open_branches.append(Sequent(seq.gamma, d_rem + [f.right], set(seq.used_insts), list(seq.domain_terms)))
                applied_rule = True; break
        if applied_rule: continue
        
        # 4. Instantiation rules (Priority: Try all EXISTING terms first)
        for i, f in enumerate(seq.gamma):
            if f.is_forall():
                for t in seq.domain_terms:
                    if (str(f), t) not in seq.used_insts:
                        new_insts = set(seq.used_insts)
                        new_insts.add((str(f), t))
                        new_gamma = seq.gamma + [f.substitute(t)]
                        open_branches.append(Sequent(new_gamma, seq.delta, new_insts, list(seq.domain_terms)))
                        applied_rule = True; break
                if applied_rule: break
        if applied_rule: continue
        
        for i, f in enumerate(seq.delta):
            if f.is_exists():
                for t in seq.domain_terms:
                    if (str(f), t) not in seq.used_insts:
                        new_insts = set(seq.used_insts)
                        new_insts.add((str(f), t))
                        new_delta = seq.delta + [f.substitute(t)]
                        open_branches.append(Sequent(seq.gamma, new_delta, new_insts, list(seq.domain_terms)))
                        applied_rule = True; break
                if applied_rule: break
        if applied_rule: continue

        # 5. Instantiation rules (Fallback: Generate a FRESH term)
        for i, f in enumerate(seq.gamma):
            if f.is_forall():
                fresh_term = f"t_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                new_domain.append(fresh_term)
                
                new_insts = set(seq.used_insts)
                new_insts.add((str(f), fresh_term))
                new_gamma = seq.gamma + [f.substitute(fresh_term)]
                open_branches.append(Sequent(new_gamma, seq.delta, new_insts, new_domain))
                applied_rule = True; break
        if applied_rule: continue
        
        for i, f in enumerate(seq.delta):
            if f.is_exists():
                fresh_term = f"t_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                new_domain.append(fresh_term)
                
                new_insts = set(seq.used_insts)
                new_insts.add((str(f), fresh_term))
                new_delta = seq.delta + [f.substitute(fresh_term)]
                open_branches.append(Sequent(seq.gamma, new_delta, new_insts, new_domain))
                applied_rule = True; break
        if applied_rule: continue

        # 6. Branch still open
        return False 

    # deque empties
    return True

def run_benchmark_suite(filename):
    print(f"Loading benchmarks from {filename}...\n")
    
    with open(filename, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    for i, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
            
        print(f"--- Problem {i+1} ---")
        print(f"Formula: {line}")
        
        try:
            # 1. Parse to AST
            parser = FOL_parser.FOLParser(line)
            ast_formula = parser.parse()
            
            # 2. ("c" is the main constant in the syntax in use)
            domain_terms = {"c"} 
            
            # 3. Run the baseline prover
            print("Proving...")
            result = prove_lk_baseline(ast_formula, domain_terms)
            
            print(f"Result: {'Provable' if result else 'Failed to prove'}\n")
            
        except Exception as e:
            print('Failed to prove\n')

if __name__ == "__main__":
    run_benchmark_suite("generated_fof_benchmarks.txt")