print("Welcome to this prover program. ")
from collections import deque
import itertools
import AST
import re
import FOL_parser
import time

class Sequent:
    def __init__(self, gamma, delta, used_insts=None, domain_terms=None, depth=0):
        self.gamma = gamma
        self.delta = delta
        self.used_insts = used_insts if used_insts is not None else set()
        self.domain_terms = domain_terms if domain_terms is not None else ["c"]
        self.depth = depth

    def is_axiom(self):
        # FAST O(1) Set Intersection for atomic predicates
        gamma_preds = {str(f) for f in self.gamma if f.is_predicate()}
        delta_preds = {str(f) for f in self.delta if f.is_predicate()}
        
        if gamma_preds.intersection(delta_preds): 
            return True
            
        if any(f.is_top() for f in self.delta): return True
        if any(f.is_bot() for f in self.gamma): return True
        return False

def prove_lk_depth_limited(formula, initial_domain, max_depth, max_steps=5000):
    init_domain = list(initial_domain) if initial_domain else []
    term_counter = itertools.count(1) 
    
    initial_sequent = Sequent(gamma=[], delta=[formula], used_insts=set(), domain_terms=init_domain, depth=0)
    open_branches = deque([initial_sequent])
    
    steps = 0
    while open_branches:
        steps += 1
        if steps > max_steps:
            return "TIMEOUT" # Prevents freezing on massively wide trees
            
        seq = open_branches.popleft()
        
        if seq.is_axiom():
            continue 
            
        applied_rule = False

        # PRIORITY 1: Non-Branching Propositional Rules (Simplifications)
        for i, f in enumerate(seq.gamma):
            if f.is_and():
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:] + [f.left, f.right]
                open_branches.append(Sequent(new_gamma, seq.delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
            elif f.is_not():
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:]
                new_delta = seq.delta + [f.inner]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
        if applied_rule: continue

        for i, f in enumerate(seq.delta):
            if f.is_or():
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.left, f.right]
                open_branches.append(Sequent(seq.gamma, new_delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
            elif f.is_implies():
                new_gamma = seq.gamma + [f.left]
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.right]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
            elif f.is_not():
                new_gamma = seq.gamma + [f.inner]
                new_delta = seq.delta[:i] + seq.delta[i+1:]
                open_branches.append(Sequent(new_gamma, new_delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
        if applied_rule: continue

        # PRIORITY 2: Branching Propositional Rules
        for i, f in enumerate(seq.gamma):
            if f.is_or():
                g_rem = seq.gamma[:i] + seq.gamma[i+1:]
                open_branches.append(Sequent(g_rem + [f.left], seq.delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                open_branches.append(Sequent(g_rem + [f.right], seq.delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
            elif f.is_implies():
                g_rem = seq.gamma[:i] + seq.gamma[i+1:]
                open_branches.append(Sequent(g_rem, seq.delta + [f.left], set(seq.used_insts), list(seq.domain_terms), seq.depth))
                open_branches.append(Sequent(g_rem + [f.right], seq.delta, set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
        if applied_rule: continue

        for i, f in enumerate(seq.delta):
            if f.is_and():
                d_rem = seq.delta[:i] + seq.delta[i+1:]
                open_branches.append(Sequent(seq.gamma, d_rem + [f.left], set(seq.used_insts), list(seq.domain_terms), seq.depth))
                open_branches.append(Sequent(seq.gamma, d_rem + [f.right], set(seq.used_insts), list(seq.domain_terms), seq.depth))
                applied_rule = True; break
        if applied_rule: continue

        # PRIORITY 3: Safe Quantifiers (Creating fresh variable)
        for i, f in enumerate(seq.gamma):
            if f.is_exists():
                fresh_var = f"e_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                if fresh_var not in new_domain: new_domain.append(fresh_var)
                new_gamma = seq.gamma[:i] + seq.gamma[i+1:] + [f.substitute(fresh_var)]
                open_branches.append(Sequent(new_gamma, seq.delta, set(seq.used_insts), new_domain, seq.depth))
                applied_rule = True; break
        if applied_rule: continue
        
        for i, f in enumerate(seq.delta):
            if f.is_forall():
                fresh_var = f"e_{next(term_counter)}"
                new_domain = list(seq.domain_terms)
                if fresh_var not in new_domain: new_domain.append(fresh_var)
                new_delta = seq.delta[:i] + seq.delta[i+1:] + [f.substitute(fresh_var)]
                open_branches.append(Sequent(seq.gamma, new_delta, set(seq.used_insts), new_domain, seq.depth))
                applied_rule = True; break
        if applied_rule: continue
        
        # PRIORITY 4: Instantiation rules (Existing terms ONLY) - DOES NOT COST DEPTH
        for i, f in enumerate(seq.delta):
            if f.is_exists():
                for t in seq.domain_terms:
                    if (str(f), t) not in seq.used_insts:
                        new_insts = set(seq.used_insts)
                        new_insts.add((str(f), t))
                        new_delta = seq.delta + [f.substitute(t)]
                        open_branches.append(Sequent(seq.gamma, new_delta, new_insts, list(seq.domain_terms), seq.depth))
                        applied_rule = True; break
                if applied_rule: break
        if applied_rule: continue

        for i, f in enumerate(seq.gamma):
            if f.is_forall():
                for t in seq.domain_terms:
                    if (str(f), t) not in seq.used_insts:
                        new_insts = set(seq.used_insts)
                        new_insts.add((str(f), t))
                        new_gamma = seq.gamma + [f.substitute(t)]
                        open_branches.append(Sequent(new_gamma, seq.delta, new_insts, list(seq.domain_terms), seq.depth))
                        applied_rule = True; break
                if applied_rule: break
        if applied_rule: continue

        # PRIORITY 5: Instantiation rules (Fresh terms - COSTS 1 DEPTH)
        if seq.depth < max_depth:
            for i, f in enumerate(seq.delta):
                if f.is_exists():
                    fresh_term = f"t_{next(term_counter)}"
                    new_domain = list(seq.domain_terms)
                    new_domain.append(fresh_term)
                    
                    new_insts = set(seq.used_insts)
                    new_insts.add((str(f), fresh_term))
                    new_delta = seq.delta + [f.substitute(fresh_term)]
                    open_branches.append(Sequent(seq.gamma, new_delta, new_insts, new_domain, seq.depth + 1))
                    applied_rule = True; break
            if applied_rule: continue

            for i, f in enumerate(seq.gamma):
                if f.is_forall():
                    fresh_term = f"t_{next(term_counter)}"
                    new_domain = list(seq.domain_terms)
                    new_domain.append(fresh_term)
                    
                    new_insts = set(seq.used_insts)
                    new_insts.add((str(f), fresh_term))
                    new_gamma = seq.gamma + [f.substitute(fresh_term)]
                    open_branches.append(Sequent(new_gamma, seq.delta, new_insts, new_domain, seq.depth + 1))
                    applied_rule = True; break
            if applied_rule: continue

        # 6. Branch remains irreconcilably open
        return False 

    return True

def prove_with_iterative_deepening(formula, initial_domain=None, absolute_max=5):
    """
    Gradually increases the depth limit of the proof search.
    """
    for current_max_depth in range(absolute_max + 1):
        result = prove_lk_depth_limited(formula, initial_domain, current_max_depth)
        
        if result == True:
            return True
        elif result == "TIMEOUT":
            # If the current depth is too massive, deeper levels will just be worse.
            print("    [Search Space Too Large - Aborting]")
            return False
            
    return False



def run_benchmark_suite(filename):
    start_time = time.perf_counter()
    print(f"Loading benchmarks from {filename}...\n")
    problem_count=0
    provable_count=0
    
    with open(filename, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    for i, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
            
        print(f"--- Problem {i+1} ---")
        print(f"Formula: {line}")
        problem_count+=1
        
        try:
            parser = FOL_parser.FOLParser(line)
            ast_formula = parser.parse()
            
            domain_terms = AST.get_constants_from_ast(ast_formula)
            
            print("Proving...")
            result = prove_with_iterative_deepening(ast_formula, domain_terms)
            
            print(f"Result: {'Provable' if result else 'Failed to prove'}\n")
            
            if result:
                provable_count+=1
            
        except Exception as e:
            print('Failed to prove\n')
            
    print (f"Proved: {provable_count} / {problem_count}")
    end_time = time.perf_counter()
    print(f"Elapsed time: {end_time - start_time:.0f} seconds")

if __name__ == "__main__":
    run_benchmark_suite("combined_benchmarks.txt")