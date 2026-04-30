import os
import re
import glob

def expand_quantifiers(match, quant_char):
    """Helper to convert TPTP's ![X,Y]: into our parser's ∀X.∀Y."""
    vars_str = match.group(1)
    vars_list = [v.strip() for v in vars_str.split(',')]
    return "".join([f"{quant_char}{v}." for v in vars_list])

def convert_tptp_to_unicode(formula_str):
    """Converts TPTP ASCII syntax into our custom Unicode syntax."""
    formula = formula_str.replace('\n', '').replace('\r', '').replace(' ', '')
    
    # ORDER MATTERS HERE! Catch the 3-character symbols before the 2-character ones.
    formula = formula.replace('<=>', '↔') # Bi-implication
    formula = formula.replace('<~>', '↮') # XOR (rare, but caught)
    formula = formula.replace('=>', '→')  # Implication
    formula = formula.replace('!=', '≠')  # Not Equals
    formula = formula.replace('&', '∧')
    formula = formula.replace('|', '∨')
    formula = formula.replace('~', '¬')
    
    formula = re.sub(r'!\[([^\]]+)\]:', lambda m: expand_quantifiers(m, '∀'), formula)
    formula = re.sub(r'\?\[([^\]]+)\]:', lambda m: expand_quantifiers(m, '∃'), formula)
    return formula

def build_formula_string(axioms, conjecture):
    if not conjecture: return None
    if not axioms: return conjecture
        
    combined_axioms = axioms[-1]
    for ax in reversed(axioms[:-1]):
        combined_axioms = f"({ax} ∧ {combined_axioms})"
        
    return f"({combined_axioms} → {conjecture})"

def harvest_tptp_folder(tptp_folder, output_filename, max_problems=500):
    print(f"Harvesting TPTP files from: {tptp_folder}...")
    
    # NEW: Grab ALL FOF files (+ without equality, = with equality)
    p_files = glob.glob(os.path.join(tptp_folder, "*+*.p")) + glob.glob(os.path.join(tptp_folder, "*=*.p"))
    
    success_count = 0
    with open(output_filename, 'w', encoding='utf-8') as out_file:
        for file_path in p_files:
            if success_count >= max_problems:
                break
                
            try: # Use try/except so one weird file doesn't crash the whole harvester
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read()
                    
                if "include(" in content:
                    continue
                    
                content = re.sub(r'%.*$', '', content, flags=re.MULTILINE)
                matches = re.findall(r"fof\s*\(\s*([^,]+)\s*,\s*([^,]+)\s*,\s*(.*?)\)\s*\.", content, flags=re.DOTALL)
                
                axioms = []
                conjecture = None
                for name, role, raw_formula in matches:
                    role = role.strip()
                    unicode_form = convert_tptp_to_unicode(raw_formula)
                    if '=' in unicode_form:
                        continue
                    if role == 'conjecture':
                        conjecture = unicode_form
                    elif role in ['axiom', 'hypothesis']:
                        axioms.append(unicode_form)
                
                if conjecture:
                    final_string = build_formula_string(axioms, conjecture)
                    if final_string:
                        out_file.write(final_string + '\n')
                        success_count += 1
            except Exception:
                pass

    print(f"\nDone! Successfully harvested {success_count} TPTP problems.")

if __name__ == "__main__":
    # Adjust paths as needed
    harvest_tptp_folder("./TPTP-v9.2.1/Problems/SYN", "tptp_benchmarks.txt", max_problems=500)