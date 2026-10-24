import InheritanceCalculus.Basic
import InheritanceCalculus.Inductive
import InheritanceCalculus.Lattice
import InheritanceCalculus.WellDefinedness
import InheritanceCalculus.Kleene
import InheritanceCalculus.Restriction
import InheritanceCalculus.Algorithm
import InheritanceCalculus.AlgorithmSoundness
import InheritanceCalculus.Certificate
import InheritanceCalculus.Interpreter
import InheritanceCalculus.PathExistence
import InheritanceCalculus.MergeSimulation
import InheritanceCalculus.MergeAssociativity
import InheritanceCalculus.MergeCommutativity
import InheritanceCalculus.MergeIdempotence
import InheritanceCalculus.ProgramMonotonicity
import InheritanceCalculus.Substitutability
import InheritanceCalculus.Decomposition
import InheritanceCalculus.Example

/-!
# Inheritance-calculus: Lean 4 formalization of the semantic layer

Formalizes, from the abstract primitive `inherits` upward, the five semantic
equations of the paper `MIXINv2/paper/inheritance-calculus.tex` and the core of
its Appendix "Well-Definedness of the Semantic Functions": monotonicity of the
immediate consequence operator, the Knaster–Tarski least fixed point, Kleene
iteration, and the path-existence lemma. The syntax layer (YAML AST and the
syntactic helpers) is out of scope by design.
-/
