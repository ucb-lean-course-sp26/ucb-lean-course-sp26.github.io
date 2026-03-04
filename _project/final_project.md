---
layout: default
title: Final Project Ideas
---

# Final Project Ideas

You are welcome to do any project you like — the lists below are just suggestions. If you are unsure whether a project idea works, you can email any of the course staff.

---

## Easy Projects

### Greedy Algorithms & Correctness
Formalize a classic greedy algorithm (e.g., Dijkstra's algorithm for shortest paths or the greedy set cover algorithm) and prove its correctness using invariants. If choosing set cover, prove the logarithmic approximation guarantee.

### Varshamov–Tenengolts (VT) Codes
Formalize VT codes, prove their single-deletion correction property, and show that their redundancy is asymptotically optimal. This involves primarily combinatorial and number-theoretic arguments.

### Asymptotic Calculation Simplification Tactic
Develop a Lean 4 tactic to automatically simplify asymptotic expressions (e.g., $O$ and $\Theta$ bounds). This could include normalization rules, dominance comparisons, and the simplification of recurrence-style expressions.

### Karp's NP-Complete Reductions
Formalize a small collection of classical NP-completeness reductions (e.g., SAT $\to$ 3SAT $\to$ Clique). Emphasize the correctness of the reductions rather than building a full formalization of polynomial time complexity.

### Johnson-Lindenstrauss Lemma
Formalize the lemma demonstrating that a set of points in a high-dimensional space can be embedded into a space of much lower dimension while nearly preserving distances. Requires formalizing probability bounds like Chernoff or Hoeffding bounds.

---

## Medium Projects

### Discrete Brascamp-Lieb Inequality
Formalize the discrete Brascamp-Lieb inequality, which generalizes classical inequalities like Hölder's and Loomis-Whitney. Involves working with entropy or information-theoretic inequalities over discrete domains.

### Karger Cut Counting Bound
Formalize bounds on the number of near-minimum cuts in a graph, which underlies Karger's randomized min-cut algorithm. This project involves combinatorics and probabilistic reasoning.

### Decision Tree Measures
Define deterministic, randomized, and certificate complexity for Boolean functions. Prove basic inequalities between these measures and analyze small example functions.

### Query Complexity
Build a formalized framework for query complexity models. Prove relationships such as degree lower bounds or the separations between deterministic, randomized, and nondeterministic query complexity.

### Communication Complexity
Formalize communication protocols and rectangle partitions. Prove lower bounds for specific functions using techniques such as fooling sets or rank arguments. Attempt to define randomized and nondeterministic communication complexity.

### Streaming Algorithms
Formalize frequency moment estimation in the streaming model, such as the Alon-Matias-Szegedy (AMS) sketch or Count Sketch. Prove their approximation guarantees and error bounds using probabilistic analysis.

### BLR Linearity Test
Formalize the Blum–Luby–Rubinfeld linearity test and prove its soundness using Fourier analysis on the Boolean cube. Connect the testing guarantees to the distance from linear functions.

### KKL Theorem (Fourier Analysis)
Formalize the Kahn-Kalai-Linial (KKL) theorem, a foundational result stating that every Boolean function has a variable with high influence. Requires setting up the Bonami-Beckner hypercontractivity inequality on the Boolean cube.

### BCH Codes Construction
Construct BCH codes using finite fields and minimal polynomials, and prove their designed distance guarantee. Requires foundational development in algebraic coding theory.

### Expander Codes
Define expander graphs and construct expander codes. Prove linear distance and the correctness of a simple decoding algorithm based on expansion properties.

### Dvir's Kakeya Set Lower Bound *(Solo-friendly)*
Formalize Dvir's polynomial method proof, which establishes a lower bound on finite-field Kakeya sets. Involves polynomial interpolation and combinatorial geometry.

### VC Theorem
Formalize VC dimension and shattering, and prove the Sauer–Shelah lemma and the VC generalization bound. Combines combinatorics with learning theory.

### Singleton-Type Bound for Locally Recoverable Codes
Formalize locally recoverable codes (LRCs) and prove a Singleton-type bound relating length, dimension, minimum distance, and locality parameter.

### Tamo-Barg Construction of LRCs
Formalize the Tamo-Barg construction of optimal locally recoverable codes using polynomial evaluation over finite fields. Prove that this construction achieves the Singleton-type bound for LRCs.

---

## Hard Projects

### Proof of Correctness of AKS Primality Algorithm
Formalize the algebraic correctness of the Agrawal-Kayal-Saxena deterministic primality test. Prove the core congruence properties in polynomial rings over finite fields without necessarily formalizing the polynomial-time computational complexity.

### Sensitivity Conjecture (Huang's Proof)
Formalize Huang's proof resolving the sensitivity conjecture using the spectral properties of subgraphs of the Boolean cube. This should include the reduction from the sensitivity conjecture to the hypercube question (bounding the maximum degree of induced subgraphs of the Boolean cube), as well as the spectral argument that resolves it. Requires the development of eigenvalue arguments and linear algebra machinery.

### Evasiveness of Monotone Graph Properties
Formalize the result that every monotone graph property is evasive (using topological or group-action arguments). This will require substantial combinatorial or topological machinery in Lean.

### Schaefer's Dichotomy Theorem
Formalize the dichotomy theorem for Boolean CSPs, proving hardness lower bounds. Use gadget reductions to avoid formally defining polynomial time (skipping the algorithmic tractability side). Requires modeling constraint languages.

### Slice Rank and Capset Bounds
Formalize the slice rank method and apply it to bound cap sets in $\mathbb{F}_3^n$. Involves tensor methods and polynomial techniques.

### MRRW Bound (Navon–Samorodnitsky Proof)
Formalize the McEliece–Rodemich–Rumsey–Welch linear programming bound using Fourier-analytic techniques in coding theory. Involves inequalities, orthogonality, and harmonic analysis on Hamming space.

### Spectral Graph Theory & Cheeger's Inequality
Formalize the discrete version of Cheeger's inequality, relating the edge expansion (or conductance) of a graph to the second smallest eigenvalue of its Laplacian matrix. Requires developing the graph Laplacian and foundational spectral bounds.
