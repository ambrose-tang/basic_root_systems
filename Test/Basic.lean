import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

noncomputable section

open Set
open Submodule

def coeff (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) : ℝ :=
  (2 * @inner ℝ E _ β α) / (@inner ℝ E _ α α)

def σ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α : E) : E ≃L[ℝ] E where
  toFun β := β - coeff E α β • α
  map_add' β₀ β₁ := by
    simp [coeff, inner_add_left, mul_add, add_div, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm, add_smul]
  map_smul' c β := by
    simp [coeff, inner_smul_left, smul_sub, ← mul_smul]
    ring_nf
  invFun β := β - coeff E α β • α
  left_inv β := by
    have hrat : ∀ x d : ℝ, (2 * (x - ((2 * x) / d) * d)) / d = -((2 * x) / d) := by
      intro x d
      by_cases hd : d = 0
      · simp [hd]
      · field_simp [hd]
        ring
    have hcoeff : coeff E α (β - coeff E α β • α) = -coeff E α β := by
      calc
        coeff E α (β - coeff E α β • α)
            = (2 * (inner ℝ β α - coeff E α β * inner ℝ α α)) / inner ℝ α α := by
                simp [coeff, inner_sub_left, inner_smul_left]
        _ = (2 * (inner ℝ β α - ((2 * inner ℝ β α) / inner ℝ α α) * inner ℝ α α)) /
              inner ℝ α α := by
              simp [coeff]
        _ = -((2 * inner ℝ β α) / inner ℝ α α) := hrat _ _
        _ = -coeff E α β := by simp [coeff]
    calc
      (β - coeff E α β • α) - coeff E α (β - coeff E α β • α) • α
          = (β - coeff E α β • α) - (-coeff E α β) • α := by simp [hcoeff]
      _ = β := by simp [sub_eq_add_neg, add_assoc]
  right_inv β := by
    have hrat : ∀ x d : ℝ, (2 * (x - ((2 * x) / d) * d)) / d = -((2 * x) / d) := by
      intro x d
      by_cases hd : d = 0
      · simp [hd]
      · field_simp [hd]
        ring
    have hcoeff : coeff E α (β - coeff E α β • α) = -coeff E α β := by
      calc
        coeff E α (β - coeff E α β • α)
            = (2 * (inner ℝ β α - coeff E α β * inner ℝ α α)) / inner ℝ α α := by
                simp [coeff, inner_sub_left, inner_smul_left]
        _ = (2 * (inner ℝ β α - ((2 * inner ℝ β α) / inner ℝ α α) * inner ℝ α α)) /
              inner ℝ α α := by
              simp [coeff]
        _ = -((2 * inner ℝ β α) / inner ℝ α α) := hrat _ _
        _ = -coeff E α β := by simp [coeff]
    calc
      (β - coeff E α β • α) - coeff E α (β - coeff E α β • α) • α
          = (β - coeff E α β • α) - (-coeff E α β) • α := by simp [hcoeff]
      _ = β := by simp [sub_eq_add_neg, add_assoc]
  continuous_toFun := by
    have hcoeff : Continuous (fun β : E => coeff E α β) := by
      simpa [coeff] using
        (((continuous_const : Continuous fun _ : E => (2 : ℝ)).mul
            (continuous_id.inner (continuous_const : Continuous fun _ : E => α))).div_const
            (inner ℝ α α) :
          Continuous fun β : E => ((2 : ℝ) * inner ℝ β α) / inner ℝ α α)
    simpa using continuous_id.sub (hcoeff.smul continuous_const)
  continuous_invFun := by
    have hcoeff : Continuous (fun β : E => coeff E α β) := by
      simpa [coeff] using
        (((continuous_const : Continuous fun _ : E => (2 : ℝ)).mul
            (continuous_id.inner (continuous_const : Continuous fun _ : E => α))).div_const
            (inner ℝ α α) :
          Continuous fun β : E => ((2 : ℝ) * inner ℝ β α) / inner ℝ α α)
    simpa using continuous_id.sub (hcoeff.smul continuous_const)

structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Φ : Set E
  W : Subgroup (E ≃L[ℝ] E) :=
    Subgroup.closure
      {σ E α | α ∈ Φ}

  -- axioms
  R1 : Set.Finite Φ ∧ Submodule.span ℝ Φ = ⊤ ∧ 0 ∉ Φ
  R2 : ∀ α : E, α ∈ Φ -> (Submodule.span ℝ ({α} : Set E) : Set E) ∩ Φ = {-α, α}
  R3: ∀ α β : E, α ∈ Φ -> β ∈ Φ -> σ E α β ∈ Φ
  R4 : ∀ α β : E, α ∈ Φ -> β ∈ Φ -> ∃n : ℤ, ↑n = coeff E α β
