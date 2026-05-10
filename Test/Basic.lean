import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

open Set
open Submodule

structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Φ : Set E
  coeff : E -> E -> ℝ := fun α β => ((2 * @inner ℝ E _ α β)/(@inner ℝ E _ α α))
  σ : E -> E -> E := fun α β => β - coeff α β • α
  W : Subgroup (Equiv.Perm E) :=
    Subgroup.closure {(⟨σ α, σ α, fun β ↦ by sorry
    , sorry⟩ : Equiv.Perm E) | α ∈ Φ}

  -- axioms
  R1 : Set.Finite Φ ∧ Submodule.span ℝ Φ = ⊤ ∧ 0 ∉ Φ
  R2 : ∀ α : E, α ∈ Φ -> (Submodule.span ℝ ({α} : Set E) : Set E) ∩ Φ = {-α, α}
  R3: ∀ α β : E, α ∈ Φ -> β ∈ Φ -> σ α β ∈ Φ
  R4 : ∀ α β : E, α ∈ Φ -> β ∈ Φ -> ∃n : ℤ, ↑n = coeff α β
