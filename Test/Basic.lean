import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

open Set
open Submodule

structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Φ : Set E
  σ : E -> E -> E := fun α β => β - ((2 * @inner ℝ E _ α β)/(@inner ℝ E _ α α)) • α
  coeff : E -> E -> ℝ := fun α β => ((2 * @inner ℝ E _ α β)/(@inner ℝ E _ α α))

  -- axioms
  R1 : Set.Finite Φ ∧ Submodule.span ℝ Φ = ⊤ ∧ 0 ∉ Φ
  R2 : ∀ α ∈ Φ, (Submodule.span ℝ ({α} : Set E) : Set E) ∩ Φ = {-α, α}
  R3: ∀ α β : E, α ∈ Φ -> β ∈ Φ -> σ α β ∈ Φ
  R4 : ∀ α β : E, α ∈ Φ -> β ∈ Φ -> ∃n : ℤ, ↑n = coeff α β
