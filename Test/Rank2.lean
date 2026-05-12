import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Test.Basic

open RootLib

notation "ℝ2" => EuclideanSpace ℝ (Fin 2)

noncomputable def A₁ : RootSystem ℝ where
  Φ := {1, -1}
  R1 := by
    constructor
    · simp
    · simp
  R2 := by
    intro α hα c
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    simp only [smul_eq_mul, Finset.mem_insert, Finset.mem_singleton]
    intro h
    cases hα <;> cases h <;> (
      first
      | exact Or.inl h
      | exact Or.inr h
      | right; nlinarith
      | left; nlinarith
    )
  R3 := by
    intro α β hα hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα hβ
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases hα <;> cases hβ <;> (
      simp [σ, coeff,
      real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, *]
      norm_num
    )
  R4 := by
    intro α β hα hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα hβ
    cases hα <;> cases hβ <;> (
      have hcoeff : coeff ℝ α β = 2 ∨ coeff ℝ α β = -2 := by
        simp [coeff, *]
      rcases hcoeff with hcoeff | hcoeff
      · exact ⟨2, by simpa using hcoeff.symm⟩
      · exact ⟨-2, by simpa using hcoeff.symm⟩
    )

noncomputable def A₁xA₁ : RootSystem ℝ2 where
  Φ :=  ({
     (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ2),
     EuclideanSpace.single (0 : Fin 2) (-1 : ℝ),
     EuclideanSpace.single (1 : Fin 2) (1 : ℝ),
     EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)
   } : Finset ℝ2)
  R1 := sorry
  R2 := sorry
  R3 := sorry
  R4 := sorry
