import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Test.Basic

open RootLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rs_invariant_fixed_P_to_negative_is_refl (rs: RootSystem E) (η : E ≃L[ℝ] E) :
  ∀ α ∈ rs.Φ, ((∀ β ∈ rs.Φ, η β ∈ rs.Φ) ∧ (∀ p ∈ P_refl E α, η p = p) ∧ (η α = -α))
  → (η = σ E α) := by
  -- Unpacking hypotheses
  intro α
  intro hα
  intro h
  rcases h with ⟨hP, hQ, hR⟩

  
