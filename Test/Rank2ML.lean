import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

open Set Module RootPairing

noncomputable section

namespace Test

abbrev A1PairingMap : ℝ →ₗ[ℝ] Module.Dual ℝ ℝ →ₗ[ℝ] ℝ := Module.Dual.eval ℝ ℝ

def A1Root : Bool ↪ ℝ where
  toFun b := if b then (1 : ℝ) else -1
  inj' := by
    intro b₁ b₂ h
    cases b₁ <;> cases b₂
    · rfl
    · have h' : (-1 : ℝ) = 1 := by simpa using h
      norm_num at h'
    · have h' : (1 : ℝ) = -1 := by simpa using h
      norm_num at h'
    · rfl

def A1Coroot : Bool ↪ Module.Dual ℝ ℝ where
  toFun b := (if b then (2 : ℝ) else -2) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  inj' := by
    intro b₁ b₂ h
    cases b₁ <;> cases b₂
    · rfl
    · have h' : ((-2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) 1 =
        ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) 1 := by
        simpa using congrArg (fun f : Module.Dual ℝ ℝ => f 1) h
      norm_num at h'
    · have h' : ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) 1 =
        ((-2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) 1 := by
        simpa using congrArg (fun f : Module.Dual ℝ ℝ => f 1) h
      norm_num at h'
    · rfl

lemma A1_root_coroot_two : ∀ i : Bool, A1PairingMap (A1Root i) (A1Coroot i) = 2 := by
  intro i
  cases i <;> norm_num [A1PairingMap, A1Root, A1Coroot]

lemma A1_mapsTo_reflections : ∀ i : Bool,
    MapsTo (Module.preReflection (A1Root i) (A1PairingMap.flip (A1Coroot i)))
      (range A1Root) (range A1Root) := by
  intro i x hx
  rcases hx with ⟨j, rfl⟩
  refine ⟨!j, ?_⟩
  cases i <;> cases j <;>
    norm_num [Module.preReflection, A1PairingMap, A1Root, A1Coroot]

lemma A1_span_root_eq_top : Submodule.span ℝ (range A1Root) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hroot : A1Root true ∈ Submodule.span ℝ (range A1Root) :=
    Submodule.subset_span ⟨true, rfl⟩
  have hx : x • A1Root true ∈ Submodule.span ℝ (range A1Root) :=
    Submodule.smul_mem _ x hroot
  convert hx using 1
  · simp [A1Root]

def A1Pairing : RootPairing Bool ℝ ℝ (Module.Dual ℝ ℝ) :=
  RootPairing.mk'' A1PairingMap A1Root A1Coroot
    A1_root_coroot_two A1_mapsTo_reflections A1_span_root_eq_top

lemma A1_crystallographic :
    ∀ i j : Bool, ∃ z : ℤ, (z : ℝ) = A1PairingMap (A1Root i) (A1Coroot j) := by
  intro i j
  cases i <;> cases j
  · refine ⟨2, ?_⟩
    norm_num [A1PairingMap, A1Root, A1Coroot]
  · refine ⟨-2, ?_⟩
    norm_num [A1PairingMap, A1Root, A1Coroot]
  · refine ⟨-2, ?_⟩
    norm_num [A1PairingMap, A1Root, A1Coroot]
  · refine ⟨2, ?_⟩
    norm_num [A1PairingMap, A1Root, A1Coroot]

instance : A1Pairing.IsRootSystem :=
  RootPairing.isRootSystem_mk''
    (p := A1PairingMap) (root := A1Root) (coroot := A1Coroot)
    (hp := A1_root_coroot_two) (hs := A1_mapsTo_reflections)
    (hsp := A1_span_root_eq_top) A1_crystallographic

end Test
