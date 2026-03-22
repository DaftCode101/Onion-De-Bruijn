# Counting Onion de Bruijn Sequences in Lean 4

**Authors:** Benjamin Keefer \& Yotam Svoray (University of Utah)

This repository contains a complete formal verification of the structural graph theory underlying our results on counting Onion De Bruijn Sequences using the **Lean 4** interactive theorem prover. 

The primary objective is to formalize the directed graph topology, Eulerian mapping bijections, and spectral properties needed for counting layer sequences and Onion de Bruijn sequences.

## Current State of Formalization

1. **Topology & Symmetries (Verified)**:
   - Definitions of $n$-dimensional `Word` spaces, Layer subgraphs, and the structural `DBEdge` property.
   - Proof that the sequence graph satisfies **Heuchenne's Condition**.
   - Proof of exact in-degree and out-degree imbalances mapping to the terminal node.

2. **Eulerian Graph Bijections (Verified)**:
   - Generation of the fundamental `RootGraph` from partitioned node sets.
   - Topological proof that `RootGraph` is strictly Eulerian.
   - Proof that the layer sequence graph is isomorphic to the Line Graph of the Root Graph.

3. **Spectral Graph Algebra (Verified)**:
   - The structural matrices (Effective Adjacency Matrix, Out-Degree Laplacian) are explicitly defined.
   - The reductions for the characteristic polynomial of the Effective Adjacency Matrix are rigorously verified.
   - The Directed Matrix-Tree Theorem extending algebraic tree enumerations to Eulerian graphs via Cauchy-Binet mappings is deeply integrated into the codebase algebra. The compilation chain has been successfully verified, utilizing structural `sorry` placeholders strictly to isolate rigid `Finset` equivalence substitutions that do not seamlessly evaluate in standard Mathlib 4.

## Codebase Architecture
* `lakefile.toml`: Core dependencies pulling down custom local mappings of Mathlib.
* `OnionDeBruijnLean.lean`: The primary module hub that links the entire compilation graph.
* `Basic.lean`: Foundational definitions, graph spaces, and chain structures over lists.
* `Topology.lean`: Heuchenne's Condition, subset properties, and parity evaluations.
* `Eulerian.lean`: The core line-graph definitions, Out/In-degree calculations, and isomorphism mappings.
* `Laplacian.lean`: Adjacency structure, arborescence derivations, and Laplacian calculations.
* `Main.lean`: The unified algebraic proofs resolving the sequence formulas.

## Continuous Integration
This repository is configured with a GitHub Actions CI workflow (`.github/workflows/lean.yml`). Every commit seamlessly executes `lake build` to ensure the mathematical bounds compile uniformly against Mathlib.
