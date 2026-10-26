/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact uniform source inlet for retained marked-squarefree subset norms.
Its conclusion is the unchanged ordinary-squarefree source contract. The
analytic projected source remains an explicit obligation; no G is assumed. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ActualEnergy

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckePrimeAnnular
open CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional CenteredMomentSourceMass
open ConcretePrimeRowBridge
open QRH.Record12518109Source QRH.Record1252270103Restoration
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

def ProjectedInitialAffineAt (face : SourceFace) (W : ℝ→ℂ)
    (a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q R₀ : Ideal O) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α,∀ (θ : T→RayQuotient.Characters rayM H)
    (w σ v : T→ℝ) (t height : ℝ),
    (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,σlo≤σ i) → (∀i,σ i≤σhi) →
    0≤height → (∀i,|v i|≤height) →
  ∀M : ℝ,Mmin≤M →M≤Mmax →
  ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
  ∀p : Profiles a b,∀X₁ X₂ : ℝ,0<X₁ →0<X₂ →
    face.Admissible (length Z X₁) (length Z X₂) (∑i,w i) M →
    let S := fun i=>primePool rayM H 2 (Z^(w i))
    let β := fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
      annularWeight W (Z^(w i)) (σ i) (v i) I
    let atoms := Finset.univ.biUnion S
    ∀rows : Finset O,projectedSubsetBound rows
      (fun z i (I : atoms)=>normalizedRowCoeff η (fixedBadMask*idealGenerator R₀) 1 z t
        (S i) (β i) (Z^(w i)) I)
      (weightedPlain η (fixedBadMask*idealGenerator R₀) 1 t (p.profile 0) (p.profile 1)
        b X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M))
      (C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
        (1+|t|+height)^degree*Z^(M+ε))

/-- The growth constant is chosen once for the ambient finite slot type.
It does not change the mesh, loss, profiles, height degree or seminorms. -/
theorem projected_initial_affine_lift (face : SourceFace) (W : ℝ→ℂ)
    (B : ℝ) (hB : 1≤B)
    (hcoef : ∀ (χ : Character) (P σ v : ℝ),1≤P →σ∈Set.Icc (33/50:ℝ) (33/50) →
      ∀I : Ideal O,‖idealCoeff χ I*annularWeight W P σ v I‖≤B)
    (a b bΦ mesh Mmin Mmax ε Z : ℝ) (hZ : 1≤Z)
    (η η₀ : Character) (Q R₀ : Ideal O) (degree : ℕ) (controls : Finset (ℕ×ℕ))
    (C : ℝ) (hC : 0≤C)
    (hsource : ProjectedInitialAffineAt (α:=α) rayM H hH face W a b bΦ mesh
      (33/50) (33/50) Mmin Mmax ε Z η η₀ Q R₀ degree controls C) :
    SquarefreeInitialAffineAt (α:=α) rayM H hH face W 2 a b bΦ mesh
      (33/50) (33/50) Mmin Mmax ε Z η η₀ Q R₀ degree controls
      ((collisionGrowth B 256 (Fintype.card α))^(Fintype.card α)*C) := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
  let S := fun i=>primePool rayM H 2 (Z^(w i))
  let β := fun i I=>idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I*
    annularWeight W (Z^(w i)) (σ i) (v i) I
  let atoms := Finset.univ.biUnion S
  have hP (i : T) : 1≤Z^(w i) := Real.one_le_rpow hZ (hw i)
  have hd := QuadraticInitialBound.diagonalControl_nonneg Φ
  have hpay : 0≤C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
      (1+|t|+height)^degree*Z^(M+ε) := by positivity
  have hb (i : T) (I : Ideal O) : ‖β i I‖≤B :=
    hcoef _ _ _ _ (hP i) ⟨hσlo i,hσhi i⟩ I
  have hsrc := hsource T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
  have hbound := squarefreeEnergy_of_projected η (fixedBadMask*idealGenerator R₀) 1 t
    (p.profile 0) (p.profile 1) b X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M)
    S β (fun i=>Z^(w i)) atoms
    (fun i I hi=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
    hX₁ hX₂ hP hΦpos B _ hB hpay (fun i I _=>hb i I)
    (fun i I hi=>(primePool_norm_le rayM H _ (zero_le_one.trans (hP i)) I hi).1)
    (fun i I hi=>(primePool_norm_le rayM H _ (zero_le_one.trans (hP i)) I hi).2)
    (Fintype.card α) (Fintype.card_subtype_le _) hsrc
  convert hbound using 1 <;> ring

def ProjectedUnitFaceSource (face : SourceFace) (mesh ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H),
  ∀W : ℝ→ℂ,ContDiff ℝ ∞ W →Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀bΦ : ℝ,2≤bΦ →∀(η η₀ : Character)(Q : Ideal O),
    Q≤rayM →internalQ Q η₀≠0 →internalQ Q η₀≠⊤ →internalQ Q η₀≤Ideal.span {(72:O)} →
  ∀R₀ : Ideal O,R₀≠0 →
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
      ∀ᶠZ : ℝ in Filter.atTop,ProjectedInitialAffineAt (α:=α) rayM H hH face W
        (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q R₀ degree controls C

theorem projected_unit_face_lift (face : SourceFace) (mesh ε : ℝ)
    (hsource : ProjectedUnitFaceSource face mesh ε) : SquarefreeUnitFaceSource face mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQ hQ0 hQt hQ72 R₀ hR₀
  obtain ⟨B,hB,hcoef⟩ := actual_annular_coefficient_bound W hW.continuous hWs (33/50) (33/50)
  obtain ⟨degree,controls,C,hC,hsrc⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q
    hQ hQ0 hQt hQ72 R₀ hR₀
  refine ⟨degree,controls,(collisionGrowth B 256 (Fintype.card α))^(Fintype.card α)*C,?_,?_⟩
  · exact mul_pos (pow_pos (zero_lt_one.trans_le (collisionGrowth_one_le B 256 _)) _) hC
  · filter_upwards [hsrc,Filter.eventually_ge_atTop (1:ℝ)] with Z hsrc hZ
    exact projected_initial_affine_lift rayM H hH face W B hB
      (fun χ P σ v hP=>hcoef χ P σ v (zero_lt_one.trans_le hP))
      (1/4) (9/4) bΦ mesh 1 1 ε Z hZ η η₀ Q R₀ degree controls C hC.le hsrc

def UniformProjectedSource (B lam cap : ℝ) : Prop :=
  ∀ε : ℝ,0<ε →∃mesh : ℝ,0<mesh ∧
    ProjectedUnitFaceSource (QRH.Record1252270103Source.globalFace B lam cap) mesh ε

theorem uniform_projected_source_lift (B lam cap : ℝ)
    (h : UniformProjectedSource B lam cap) : UniformSquarefreeUnitFaceSource B lam cap := by
  intro ε hε
  obtain ⟨mesh,hm,hs⟩ := h ε hε
  exact ⟨mesh,hm,projected_unit_face_lift _ mesh ε hs⟩

end
end QRH.Record1252270103Source.Collision

#print axioms QRH.Record1252270103Source.Collision.projected_initial_affine_lift
#print axioms QRH.Record1252270103Source.Collision.projected_unit_face_lift
#print axioms QRH.Record1252270103Source.Collision.uniform_projected_source_lift
