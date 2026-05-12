import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic
import Test.Basic
import Mathlib.Algebra.Quotient

open RootLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ℝ_α (α : E) : Subspace ℝ E:= Submodule.span ℝ {α}

theorem rs_invariant_fixed_P_to_negative_is_refl (rs: RootSystem E) (η : E ≃L[ℝ] E) :
  ∀ α ∈ rs.Φ, ((∀ β ∈ rs.Φ, η β ∈ rs.Φ) ∧ (∀ p ∈ P_refl E α, η p = p) ∧ (η α = -α))
  → (η = σ E α) := by
  intro α hα h
  rcases h with ⟨hP, hQ, hR⟩

  let τ := fun β => η (σ E α β)

  have hΦ : ∀ β : E, β ∈ rs.Φ → τ β ∈ rs.Φ := by
    intro β hβ
    apply hP
    exact rs.R3 α β hα hβ

  have hτ : τ α = α := by
    simp only [τ, refl_a_a_neg E α]
    have : η (-α) = -η α := by simp
    simp only [map_neg]
    rw [hR]
    simp

  have hℝ : ∀ k : ℝ, τ (k • α) = k • α := by
    simp [τ, hτ]

  let ηq : (E ⧸ (ℝ_α α)) → (E ⧸ (ℝ_α α)) := fun v =>
    Quotient.map η (fun a b hab => by
      show η a - η b ∈ (ℝ_α α)
      have : a - b ∈ (ℝ_α α) := hab
      have : η (a - b) ∈ (ℝ_α α) := by
        rw [map_sub]
        exact Submodule.map_mem_of_mem _ this
      simp [map_sub] at this
      exact this
    ) v

  sorry
