# TransitionSystems

Some proofs relating different types of simulation for (hardware-based) transition systems.

A Lean-formalization of [A Framework for Microprocessor Correctness Statements](http://dx.doi.org/10.1007/3-540-44798-9_33).
Following along with the paper, we model various forms of alignment for a generic match relation.
Unlike the paper, we
  1. consider relationships between the *inputs* to the specification and implementation transition systems
  2. restrict the specification and implementation to both be deterministic
