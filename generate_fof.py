import os

def combine_with_and(formulas):
    """Helper to strictly strictly binarize a list of formulas with ANDs."""
    if not formulas: return ""
    if len(formulas) == 1: return formulas[0]
    block = formulas[-1]
    for p in reversed(formulas[:-1]):
        block = f"({p} ∧ {block})"
    return block

def gen_universal_chain(n):
    """Tests ForAll L, Implies L/R, And L"""
    premises = [f"∀x.(P{i}(x) → P{i+1}(x))" for i in range(n)]
    premise_block = combine_with_and(premises)
    full_premise = f"({premise_block} ∧ P0(c))"
    return f"({full_premise} → P{n}(c))"

def gen_existential_chain(n):
    """Tests Exists L/R (eigenvariables), ForAll L, Implies."""
    # Premise 1: ∃x.P0(x)
    # Premise 2: ∀x.(P0(x) → ∃y.P1(y)) ...
    # Conclusion: ∃x.Pn(x)
    premises = ["∃x.P0(x)"]
    for i in range(n):
        premises.append(f"∀x.(P{i}(x) → ∃y.P{i+1}(y))")
    
    full_premise = combine_with_and(premises)
    return f"({full_premise} → ∃z.P{n}(z))"

def gen_demorgans_quantifiers(n):
    """Tests Not L/R, ForAll, Exists inversion."""
    # ¬(∀x1.∀x2... P(x1,x2...)) → ∃x1.∃x2... ¬P(x1,x2...)
    variables = [f"x{i}" for i in range(n)]
    args = ", ".join(variables)
    
    left_side = f"P({args})"
    right_side = f"¬(P({args}))"
    
    # Wrap left side in ForAlls
    for var in reversed(variables):
        left_side = f"∀{var}.{left_side}"
    left_side = f"¬({left_side})"
    
    # Wrap right side in Exists
    for var in reversed(variables):
        right_side = f"∃{var}.{right_side}"
        
    return f"({left_side} → {right_side})"

def gen_branching_explosion(n):
    """Tests Or L, And R (Branching rule explosion)."""
    # ((A1 ∨ B1) ∧ (A2 ∨ B2) ...) → ((A1 ∧ A2 ...) ∨ (B1 ∨ B2 ...))
    # This creates 2^n branches in a naive prover!
    left_pairs = [f"(A{i} ∨ B{i})" for i in range(1, n+1)]
    left_side = combine_with_and(left_pairs)
    
    a_preds = [f"A{i}" for i in range(1, n+1)]
    b_preds = [f"B{i}" for i in range(1, n+1)]
    
    # Binarize the right side ORs and ANDs
    a_block = a_preds[-1]
    for p in reversed(a_preds[:-1]): a_block = f"({p} ∧ {a_block})"
        
    b_block = b_preds[-1]
    for p in reversed(b_preds[:-1]): b_block = f"({p} ∨ {b_block})"
        
    right_side = f"({a_block} ∨ {b_block})"
    
    return f"({left_side} → {right_side})"

def generate_comprehensive_benchmarks(filename):
    print(f"Generating comprehensive benchmark dataset: {filename}")
    
    with open(filename, 'w', encoding='utf-8') as f:
        for n in range(1, 6):
            f.write(gen_universal_chain(n) + '\n')
            
        for n in range(1, 6):
            f.write(gen_existential_chain(n) + '\n')
            
        for n in range(1, 6):
            f.write(gen_demorgans_quantifiers(n) + '\n')
            
        for n in range(1, 6): # n=6 creates 64 branches, n=10 creates 1024!
            f.write(gen_branching_explosion(n) + '\n')

    print("Generation complete. This dataset will thoroughly test all LK rules.")

if __name__ == "__main__":
    generate_comprehensive_benchmarks("generated_fol_benchmarks.txt")