import Candidate.Lib.PadicHodge.Crystalline.HodgeTateFrame

-- Options from the original lakefile.toml [leanOptions]
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option maxHeartbeats 4000000

/-! Part of: Limits of crystalline representations with bounded weights are crystalline (known
result; see Lib.PadicHodge.Limit.LocalLimit).

This file: A_max periods embed in B_max periods; crystalline with weights in [0,h]; bundled
representations. -/


open TensorProduct Module
variable {p} [ThePrime p] {Γ T R : Type} [Group Γ] [OverGp Γ p] [AddCommGroup T] [Module ℤ_[p] T]
  [CommRing R] [Module R T] [Algebra ℤ_[p] R] [IsScalarTower ℤ_[p] R T]

lemma periodTensorMap_injective [Flat ℤ_[p] T] : (periodTensorMap _ _ .id : Amax ⊗[_] T →
  Bcris ⊗ T).Injective := Flat.rTensor_preserves_injective_linearMap (Algebra.algHom ..).toLinearMap
  (injective_BPlus_Bcris.comp injective_Amax_BPlus)

/-- The representation is crystalline and all its Hodge–Tate jumps, at every γ: R → C_p, lie in
[0, h]. -/
def IsCrystallineUpTo (h : ℕ) (ρ : Representation R Γ T) := IsCrystalline ρ ∧ ∀ γ k,
  jump ρ γ k ≠ 0 → 0 ≤ k ∧ k ≤ h

/-- A representation of Γ over Q̄_p of some finite dimension: a finite index type m with a group
homomorphism r from Γ to GL_m(Q̄_p), with no continuity required. -/
structure PadicRep Γ [Group Γ] p [ThePrime p] where
  {Index : Type} [fintypeIndex : Fintype Index] (rep : Γ →* GL Index (PadicAlgCl p))

attribute [instance] PadicRep.fintypeIndex

/-- For a Z_p-linear map u from T to square matrices over Q̄_p and a vector v, the Z_p-linear
map sending x to u(x)v. -/
noncomputable abbrev applyVec {m} [Fintype m] (u : T →ₗ[ℤ_[p]] Matrix m m (PadicAlgCl p)) v :=
  (Matrix.mulVecBilin _ ℤ_[p]).flip v ∘ₗ u
