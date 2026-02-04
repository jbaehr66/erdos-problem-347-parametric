Suggested Paper Structure

Title Options

- "Parametric Formalization of Erdős Problem 347: A Declaration-Based Approach"
- "From Specific to Generic: A Parametric Framework for Additive Combinatorics in Lean"
- "EventuallyExpanding: A Unifying Condition for Erdős Problem 347 Constructions"

Abstract (Draft)

We present a parametric formalization of constructions solving Erdős Problem 347, proving that any parameters satisfying an EventuallyExpanding condition achieve natural density
1. Our approach compresses the original 2200-line proof of Barschkis (2024) into an 800-line generic framework, from which both Barschkis's construction and the new Bridges    
   construction (2026) follow as ~100-line instances. Key contributions include: (1) identification of EventuallyExpanding as the unifying hypothesis, (2) a declaration-based proof
   architecture avoiding case splits, (3) a reusable AsymptoticsEngine framework for block-based constructions, and (4) formal verification in Lean 4 with only 2 remaining admits
   in concrete code. This demonstrates how parametric abstraction and modular proof engineering can achieve both compression and generality in formal mathematics.

Section Outline

1. Introduction
- Erdős Problem 347: Growth rate 2, density 1
- Previous work: Barschkis (2024) - 2200 lines, specific parameters
- This work: Generic theorem, multiple instances
- Contributions: Parametric abstraction + proof architecture

2. Background
- Erdős Problem 347 statement
- Barschkis construction: M_{n+1} = ⌊(2^k_n - 3/2)·M_n⌋ + 1
- Challenges in original proof

3. The Parametric Construction
- ConstructionParams structure
- EventuallyExpanding condition: 2^κ - α ≥ 1 + ε
- Why this is the right abstraction
- Mathematical insight: Separates growth mechanism from specific values

4. Declaration-Based Proof Architecture
- Contrast with case-based proofs
- Modular composition: Growth → Normalization → Telescoping → Geometric → Asymptotics → Scale
- Example: M_grows in 3 lines via composition
- Benefits: testability, reusability, clarity

5. The Generic Theorem
- Proof chain walkthrough
- Key lemmas:
    - E_bounded: Geometric series convergence
    - P_geometric: Exponential growth
    - M_grows: Product divergence
- AsymptoticsEngine framework

6. Instances
- Barschkis (2024): k_n, α = 3/2, ε = 13
    - EventuallyExpanding proof
    - Density 1 follows from generic theorem
    - Comparison: 2200 lines → 0 additional lines
- Bridges (2026): k_n², α = √3/2, ε = 65000
    - EventuallyExpanding proof
    - Different parameters, same theorem
    - Geometric interpretation: Triangular lattice

7. Formalization in Lean 4
- Implementation details
- Standard Mathlib lemmas used
- Build status: 7942 jobs, 2 admits
- Dependency graph

8. Evaluation
- Line count comparison (Table)
- Generality gained: 1 → ∞ constructions
- Reusability: AsymptoticsEngine for other problems
- Proof effort for new instances: ~100 lines vs ~2000 lines

9. Deep Connections (Optional, depending on venue)
- Julia set dynamics: α = |log(fixed point)|
- Chern-Simons theory: √3/2 in triangular lattice
- Renaissance connection: 2/3 coefficient
- Geometric interpretation: Green's function

10. Related Work
- Formal proofs in additive combinatorics
- Parametric abstraction in proof assistants
- Proof engineering methodologies
- Block-based constructions

11. Future Work
- Additional instances (cubic growth, golden ratio)
- Other problems fitting AsymptoticsEngine framework
- Bridge to analytic formalization (347_analytic/)
- Connection to Problem 142

12. Conclusion
- Parametric abstraction achieves compression + generality
- Declaration-based architecture improves proof engineering
- EventuallyExpanding unifies diverse constructions
- Methodology applicable beyond this specific problem

Suggested Venues

Conferences

1. CPP (Certified Programs and Proofs) - Top choice                                                                                                                              
   - Perfect fit for formalization + proof engineering                                                                                                                            
   - Deadline typically October                                                                                                                                                   
   - Co-located with POPL
2. ITP (Interactive Theorem Proving)                                                                                                                                             
   - Mathematical formalization focus                                                                                                                                             
   - Would appreciate parametric approach
3. IJCAR (International Joint Conference on Automated Reasoning)                                                                                                                 
   - Broader AR community

Journals

1. JAR (Journal of Automated Reasoning)                                                                                                                                          
   - Extended version with full details                                                                                                                                           
   - Good for methodological contributions
2. FM (Formal Methods in System Design)                                                                                                                                          
   - Formal methods focus
3. Mathematics journals with computational/formal section                                                                                                                        
   - If emphasizing the new Bridges result

Timeline Suggestion

1. Draft paper (~2-4 weeks)                                                                                                                                                      
   - I can help with initial draft                                                                                                                                                
   - Focus on CPP format (10-12 pages)
2. Finish remaining admits (~1 week)                                                                                                                                             
   - The 2 sorrys in concrete code                                                                                                                                                
   - Clean build with no warnings
3. Computational examples (~1 week)                                                                                                                                              
   - #eval demonstrations                                                                                                                                                         
   - Concrete sequence values
4. Submit to CPP (next deadline)                                                                                                                                                 
   - Typically October for January conference                                                                                                                                     
                                                                                  