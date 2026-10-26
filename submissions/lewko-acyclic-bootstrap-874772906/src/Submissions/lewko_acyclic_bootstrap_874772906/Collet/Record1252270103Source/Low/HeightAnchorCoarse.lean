/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine all-height coarse initial energy on the global face; the fixed mask,
squarefree ordinary projector and marked projection are restored explicitly. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyParentUniform
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialAssemblyCanonical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialCoarse
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low.HeightAnchor
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentDetectorEnergyInitialState QuadraticInitialBound
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Record1252270103Source QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O

lemma coarse_plain_cap {B Z X : ℝ} (hB : B≤1) (hZ : 1<Z) (hL : length Z X≤B) :
    X≤Z^(2:ℝ) := by
  apply (le_max_right 1 X).trans
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mp
  change length Z X≤2
  linarith

theorem ordinary_coarse_global (B lam cap mesh : ℝ) (hB : B≤1) (hm : 0≤mesh)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (N : ℕ) (α : Type) [Fintype α] [DecidableEq α] (hN : Fintype.card α≤N)
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2≤bΦ) (η η₀ : Character) (Q : Ideal O)
    (hQM : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    InitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W 2 (1/4) (9/4)
      bΦ mesh (33/50) (33/50) 1 1 (1+2*(N:ℝ)*mesh) Z η η₀ Q degree controls C := by
  obtain ⟨degree,S,hs⟩:=Cycle61Physical.original_initial_coarse (α:=α) rayM H hH W
    1 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 1
    (by norm_num) hsW hW (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by linarith) hm (by norm_num) le_rfl (by norm_num) le_rfl hbeta (fun _ : Unit=>η)
  obtain ⟨C,hC,hs⟩:=hs η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,S,C,hC,hs.mono ?_⟩
  intro Z hZ T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hsΦ hΦ
    p X₁ X₂ hX₁ hX₂ hadm
  have hM : M=1:=by linarith
  subst M
  have hl₁ : length Z X₁≤B := by simpa [globalFace] using hadm.2.1
  have hl₂ : length Z X₂≤B := by simpa [globalFace] using hadm.2.2.2.1
  have hc:=hZ.2 () T θ w σ v t height hw hwm hσlo hσhi hh 1 le_rfl le_rfl
    Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ (by convert coarse_plain_cap hB hZ.1 hl₁ using 1 <;> norm_num) (by convert coarse_plain_cap hB hZ.1 hl₂ using 1 <;> norm_num)
  have hcard : (Fintype.card α:ℝ)≤N := by exact_mod_cast hN
  have hex : 1+(1+2*(Fintype.card α:ℝ)*mesh)≤1+(1+2*(N:ℝ)*mesh) := by nlinarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.1.le hex
  change Cycle61Physical.initialEnergy rayM H hH W 2 Z 1 η η₀ Q T θ w σ v t X₁ X₂
    (p.profile 0) (p.profile 1) Φ≤_
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by
    have hd:=diagonalControl_nonneg Φ
    positivity))

theorem projected_coarse_global (B lam cap mesh : ℝ) (hB : B≤1) (hlam : 0≤lam) (hm : 0≤mesh)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (α : Type) [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2≤bΦ) (η η₀ : Character) (Q R₀ : Ideal O)
    (hQM : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (hR₀ : R₀≠0) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ProjectedInitialAffineAt (α:=α) rayM H hH (globalFace B lam cap) W (1/4) (9/4)
      bΦ mesh (33/50) (33/50) 1 1 ((1+2*(Fintype.card α:ℝ)*mesh)+2*1) Z η η₀ Q R₀ degree controls C := by
  let ε : ℝ:=1+2*(Fintype.card α:ℝ)*mesh
  let δ : ℝ:=1
  have hδ : 0<δ:=by norm_num [δ]
  have hs (T : Finset α):=ordinary_coarse_global B lam cap mesh hB hm hbeta (Fintype.card α) T
    (by simpa using Finset.card_le_univ T) rayM H hH W hW hsW bΦ hbΦ η η₀ Q hQM hQ0 hQt hQ72
  choose dj Sj Cj hCj hj using hs
  have hp (T : Finset α):=canonical_projected_parent (α:=T) rayM H hH W hsW hW δ hδ
  choose Aj hAj hp using hp
  let D:=∑T : Finset α,dj T
  let S:=Finset.univ.biUnion Sj
  let a:=fun T : Finset α=>Aj T*(R₀.radical.absNorm:ℝ)^δ*Cj T
  have ha (T : Finset α) : 0≤a T:=
    mul_nonneg (mul_nonneg (hAj T).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hCj T).le
  let C:=1+∑T : Finset α,a T*2^(dj T)
  have hC : 0<C:=by
    have hsum:=Finset.sum_nonneg (s:=Finset.univ)
      (fun T _=>mul_nonneg (ha T) (by positivity : 0≤(2:ℝ)^(dj T)))
    dsimp [C];linarith
  have hd (T : Finset α) : dj T≤D:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hS (T : Finset α) : Sj T⊆S:=fun _ hx=>Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hCC (T : Finset α) : a T*2^(dj T)≤C := by
    have hh:=Finset.single_le_sum (fun U _=>mul_nonneg (ha U) (by positivity : 0≤(2:ℝ)^(dj U)))
      (Finset.mem_univ T)
    dsimp [C];linarith
  refine ⟨D,S,C,hC,?_⟩
  have hall : ∀ᶠZ : ℝ in atTop,∀T : Finset α,_:=Filter.eventually_all.mpr hj
  filter_upwards [hall,eventually_ge_atTop (6:ℝ)] with Z hsrc hZ6
  intro T θ w σ v t height hw hmesh hσlo hσhi hh hv M hMlo hMhi Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ hadm
  have hM : M=1:=by linarith
  subst M
  have hσ : σ=(fun _=>33/50):=funext (fun i=>le_antisymm (hσhi i) (hσlo i))
  subst σ
  have hZ : 1<Z:=by linarith
  have hw0 : 0≤∑i,w i:=Finset.sum_nonneg (fun i _=>hw i)
  have hcap : (∑i,w i)≤cap:=by simpa [globalFace] using hadm.2.2.2.2.2.1
  have hbudget : length Z X₁+length Z X₂+lam*(∑i,w i)≤B:=by
    simpa [globalFace] using hadm.2.2.2.2.2.2
  have hcut : (9/4:ℝ)^2*X₁*X₂≤Z^(2:ℝ) := by
    have h:=global_reference_cutoff B lam cap Z X₁ X₂ (∑i,w i) 0 hZ6 hX₁ hX₂ hlam hw0 hB hadm
    simpa only [Real.rpow_zero,div_one,mul_one,mul_assoc] using h
  have hparent:=hp T B lam cap (1/4) (9/4) bΦ mesh ε Z hlam (by norm_num) (by norm_num) hZ
    η η₀ Q (dj T) (Sj T) (Cj T) (hCj T).le (hsrc T) θ w v t height hw hmesh hh hv
    hcap p X₁ X₂ hX₁ hX₂ hbudget hcut Φ hsΦ hΦ R₀ hR₀
  have hpow : (Z^δ)^2*Z^(1+ε)=Z^(1+(ε+2*δ)) := by
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le δ 2,
      ←Real.rpow_add (zero_lt_one.trans hZ)]
    congr 1
    norm_num
    ring
  dsimp only
  intro rows J _ f
  simp only [Real.rpow_one]
  refine (hparent rows J f).trans ?_
  calc
    _=a T*diagonalControl Φ*(p.control (Sj T))^2*(1+|t|+height)^(dj T)*Z^(1+(ε+2*δ)) := by
      rw [←hpow]
      dsimp [a]
      ring
    _≤a T*diagonalControl Φ*(p.control (Sj T))^2*(1+|t|+|t|+height)^(dj T)*Z^(1+(ε+2*δ)) := by
      have hh0 : 0≤1+|t|+height:=by positivity
      have hh1 : 1+|t|+height≤1+|t|+|t|+height:=by linarith [abs_nonneg t]
      have hdiag:=diagonalControl_nonneg Φ
      have haT:=ha T
      gcongr
    _≤_:=source_control_promote p Φ (Sj T) S (hS T) (dj T) D (hd T) (a T) C t height Z
      (1+(ε+2*δ)) (ha T) (hCC T) hh (zero_lt_one.trans hZ).le


theorem marked_coarse_global (B lam cap mesh : ℝ) (hB : B≤1) (hlam : 0≤lam) (hm : 0≤mesh)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (α : Type) [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hsW : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 2≤bΦ) (η η₀ : Character) (Q R₀ : Ideal O)
    (hQM : Q≤rayM) (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (hR₀ : R₀≠0) :
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    CanonicalMarkedAt (α:=α) rayM H hH (globalFace B lam cap) W hW hsW
      bΦ mesh ((1+2*(Fintype.card α:ℝ)*mesh)+2*1) Z η η₀ Q R₀ degree controls C := by
  obtain ⟨d,S,C,hC,hs⟩:=projected_coarse_global B lam cap mesh hB hlam hm hbeta
    α rayM H hH W hW hsW bΦ hbΦ η η₀ Q R₀ hQM hQ0 hQt hQ72 hR₀
  refine ⟨d,S,C,hC,hs.mono ?_⟩
  intro Z hs hZ T θ w v t height hw hwm hh hv p X₁ X₂ hX₁ hX₂ hadm rows Φ hsΦ hΦ
  have hp:=hs T θ w (fun _=>33/50) v t height hw hwm (fun _=>le_rfl) (fun _=>le_rfl)
    hh hv 1 le_rfl le_rfl Φ hsΦ hΦ p X₁ X₂ hX₁ hX₂ hadm
  simp only [Real.rpow_one] at hp
  let s:=initialInput rayM H hH W hW hsW Z (zero_lt_one.trans hZ) η η₀ R₀ θ w v t
    p (by norm_num) X₁ X₂ X₁ X₂ hX₁ hX₂ hX₁ hX₂ rfl
  let atoms:=Finset.univ.biUnion s.slots
  have hSlots (i : T) : s.slots i⊆atoms:=fun I hI=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hI⟩
  have hPrime : ∀I∈atoms,Prime I := by
    intro I hI
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hI
    exact (Finset.mem_filter.mp hi).2.1
  exact markedFiniteEnergy_le_projected s R₀ 1 (9/4) X₁ X₂ hX₁ hX₂ rows
    (initialKeep η (internalQ Q η₀)) Φ Z hΦ atoms hSlots hPrime _ (hp rows)
end
end QRH.Record1252270103Low.HeightAnchor
#print axioms QRH.Record1252270103Low.HeightAnchor.ordinary_coarse_global
#print axioms QRH.Record1252270103Low.HeightAnchor.projected_coarse_global
#print axioms QRH.Record1252270103Low.HeightAnchor.marked_coarse_global
