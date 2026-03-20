# Counting Onion de Bruijn Sequences in Lean 4

**Authors:** Benjamin Keefer \& Yotam Svoray (University of Utah)
This repository contains a formal verification of the structural and spectral graph theory underlying our results on counting Onion De Bruijn Sequences using the **Lean 4** interactive theorem prover.

The primary objective of this project is to rigorously formalize the directed graph topology, the Eulerian mapping bijections, and the characteristic spectral algebra necessary to derive the deterministic counting formulas for $(n, k)$ layer sequences and Onion de Bruijn sequences.

## Verified Results
This repository achieves a `sorry`-free compilation of the core graph-theoretic pipeline. Lean 4 has definitively verified the following mathematical components:

1. **Topology & Symmetries**:
   - Explicit definitions of the $n$-dimensional `Word` spaces, Layer subgraphs, and the structural `DBEdge` property.
   - The algorithmic confirmation that the sequence graph precisely satisfies **Heuchenne's Condition** (Theorem 2.2).
   - The definitive proof of the exact in-degree and out-degree imbalances mapping directly to the terminal node (Observation 2.1).

2. **Eulerian Graph Bijections**:
   - The generation of the fundamental `RootGraph` from partitioned node sets.
   - The topological proof that `RootGraph` is strictly Eulerian (Lemma 3.2), verified via finite-element bijective mapping.
   - The proof that the layer sequence graph is mathematically isomorphic to the Line Graph of the Root Graph (Lemma 3.3).

3. **Spectral Graph Algebra**:
   - The explicit extraction of algebraic characteristic bounds from the $L \times L$ Effective Adjacency Matrices.
   - The exact algebraic derivations resolving the total number of layer sequences (Proposition 4.5) and total Onion sequences (Theorem 5.1).

## Formalization Boundaries (Axioms)
Because constructing the entirety of combinatorial Abstract Algebra from scratch in Lean is outside the immediate scope of this graph-theory formalization, this repository leverages `axiom` definitions to bridge standard foundational theorems into the final formula:

1. **BEST Theorem & Matrix-Tree Theorem**: The extraction of spanning arborescences from the sub-Laplacian characteristic polynomial is axiomatized. Lean 4's `mathlib4` does not yet possess standard library support for directed-graph spectral counting.
2. **Burnside's Lemma**: The final integer divisibility, scaling the sequences into cyclical rotational bounds (Corollary 5.2), invokes Burnside's Lemma as a boundary axiom.

> **Context on Axiomatization:** 
> The explicit axiomatization of the Directed Matrix-Tree step is a deliberate architectural boundary. As of mid-2024, the BEST Theorem remains unformalized within the Lean 4 `mathlib4` ecosystem (listed prominently on the community's *100 Theorems to Formalize* wishlist). By successfully proving the novel Onion topological structures and Eulerian Line-Graph bounds internally, this repository formally bridges the core paper's novelty directly to the current limits of open-source automated theorem provers.

## Codebase Architecture
* `lakefile.toml`: Core dependencies pulling down custom local mappings of Mathlib.
* `OnionDeBruijnLean.lean`: The primary module hub that links the entire compilation graph.
* `Basic.lean`: Foundational definitions, graph spaces, and chain structures over lists.
* `Topology.lean`: Heuchenne's Condition, subset properties, and parity evaluations.
* `Eulerian.lean`: The core line-graph definitions, Out/In-degree calculations, and isomorphism mappings.
* `Laplacian.lean`: Adjacency structure, arborescence derivations, and Laplacian root calculations.
* `Main.lean`: The unified algebraic proofs explicitly mapping the sequence formulas.

## Continuous Integration
This repository is configured with a GitHub Actions CI workflow (`.github/workflows/lean.yml`). Every commit automatically provisions an isolated `elan` compilation cluster and seamlessly executes `lake build` to ensure the mathematical bounds compile uniformly against Mathlib.
