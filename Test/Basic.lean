import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

noncomputable section

open Set
open Submodule

def coeff (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) : ℝ :=
  (2 * @inner ℝ E _ α β) / (@inner ℝ E _ α α)

def σ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) : E :=
  β - coeff E α β • α

lemma coeff_sub (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) :
    coeff E α (β - coeff E α β • α) = -coeff E α β := by
  unfold coeff
  rw [inner_sub_right, inner_smul_right]
  simp
  by_cases hα : ‖α‖ = 0
  · simp [hα]
  · have hα2 : ‖α‖ ^ 2 ≠ 0 := by exact pow_ne_zero 2 hα
    field_simp [hα2]
    ring

lemma σ_involutive (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α : E) :
    Function.Involutive (σ E α) := by
  intro β
  change β - coeff E α β • α - coeff E α (β - coeff E α β • α) • α = β
  rw [coeff_sub]
  simp [sub_eq_add_neg, add_assoc]

structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Φ : Set E
  W : Subgroup (Equiv.Perm E) :=
    Subgroup.closure
      {(⟨σ E α, σ E α, σ_involutive E α, σ_involutive E α⟩ :
          Equiv.Perm E) | α ∈ Φ}

  -- axioms
  R1 : Set.Finite Φ ∧ Submodule.span ℝ Φ = ⊤ ∧ 0 ∉ Φ
  R2 : ∀ α : E, α ∈ Φ -> (Submodule.span ℝ ({α} : Set E) : Set E) ∩ Φ = {-α, α}
  R3: ∀ α β : E, α ∈ Φ -> β ∈ Φ -> σ E α β ∈ Φ
  R4 : ∀ α β : E, α ∈ Φ -> β ∈ Φ -> ∃n : ℤ, ↑n = coeff E α β

