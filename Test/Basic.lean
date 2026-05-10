import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Basic

noncomputable section

open Set
open Submodule

def coeff (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) : ℝ :=
  (2 * @inner ℝ E _ α β) / (@inner ℝ E _ α α)

def σ_formula (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α β : E) : E :=
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
    Function.Involutive (σ_formula E α) := by
  intro β
  change β - coeff E α β • α - coeff E α (β - coeff E α β • α) • α = β
  rw [coeff_sub]
  simp [sub_eq_add_neg, add_assoc]

def σ_elem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (α : E) :
    Equiv.Perm E :=
  ⟨σ_formula E α, σ_formula E α, σ_involutive E α, σ_involutive E α⟩

@[simp] lemma sigma_elem_apply {E : Type*}
[NormedAddCommGroup E] [InnerProductSpace ℝ E]
     (α x : E) :
     σ_elem E α x = σ_formula E α x := rfl

structure RootSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Φ : Set E
  W : Subgroup (Equiv.Perm E) :=
    Subgroup.closure
      {σ_elem E α | α ∈ Φ}

  -- axioms
  R1 : Set.Finite Φ ∧ Submodule.span ℝ Φ = ⊤ ∧ 0 ∉ Φ
  R2 : ∀ α : E, α ∈ Φ -> (Submodule.span ℝ ({α} : Set E) : Set E) ∩ Φ = {-α, α}
  R3: ∀ α β : E, α ∈ Φ -> β ∈ Φ -> σ_formula E α β ∈ Φ
  R4 : ∀ α β : E, α ∈ Φ -> β ∈ Φ -> ∃n : ℤ, ↑n = coeff E α β

theorem map_refl_invmap_is_map_refl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (rs : RootSystem E)
    (η : Equiv.Perm E) (hη : η ∈ rs.W)
    (α : E) (hα : α ∈ rs.Φ) (β : E) (hβ : β ∈ rs.Φ) :
  η * σ_elem E α * η⁻¹ = σ_elem E β := by
  have hσ : (η * σ_elem E α * η⁻¹) (η β) = (η β) - coeff E α β • (η α) := by sorry
  sorry
