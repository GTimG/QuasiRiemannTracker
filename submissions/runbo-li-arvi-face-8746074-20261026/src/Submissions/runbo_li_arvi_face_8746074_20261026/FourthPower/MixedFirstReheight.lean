/- Copyright (c) 2026 Sil. Apache-2.0.
Exact midpoint recanonicalization of independent source and row heights.
The literal finite rows
differ by one unit scalar, so all retained and grouped energies agree. The checked chosen energy estimate is then transferred to independent heights.
All source geometry and selected weights are preserved.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstReferenceDispatch
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstChosenEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstReheight
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAddedZeroUniform CenteredMomentCommonMaskEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceLiveColumn
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstSectors
open CenteredMomentCommonProfile CenteredMomentNaturalFixedRaySource
open CenteredMomentLattice CenteredMomentAllocatedNaturalRadial
open CenteredMomentOriginalRadialComparison
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalHeights MixedPrincipalWindow
open MixedCommonHeights MixedHeightEnergy MixedCommonCoefficient MixedCompletedRows
open MixedCommonRestriction MixedLiteralAllocation MixedSupplierSource
open MixedFirstPhysicalApplication MixedFirstSeededEnergy MixedFirstAvoidance
open MixedFirstReferenceDispatch MixedFirstActualNonexceptional MixedCanonicalSource
open MixedFirstProfileEnvelope
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α ⊕ Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The arbitrary seed, original prefixes, literal tupleWeight, and every
marked slot are retained. This identity holds even at the zero ideal. -/
theorem source_coefficient_shift (s : Source ι a b) (ha : 0<a)
    (seed I : Id) (v : ℝ) :
    sourceCoefficient s ha seed I * idealHeight v I =
      residualPhase (s.X₁*s.X₂) s.d 1 v *
        sourceCoefficient (shiftSource s v) ha seed I := by
  let Q := Fintype.piFinset (tuplePools s)
  have hQ : ∀q∈Q,∀j,q j≠0 := by
    intro q hq j
    exact source_pools_nonzero s.pool s.hp s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂
      j _ (Fintype.mem_piFinset.mp hq j)
  have he := residual_column_height Q hQ (tupleWeight (punctureProduct s.S s.H))
    s.R seed 1 one_ne_zero s.ν s.Wslot s.P s.W₁ s.W₂
    (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi)) v s.X₁ s.X₂ s.Y₁ s.Y₂
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂)
    (s.hpX.trans s.hpY.symm) s.d s.hd I
  simpa only [Q,tuplePools,sourceCoefficient,originalColumn,shiftSource,
    norm_power_profile_phase,add_div,one_mul] using he

/-- This is a pointwise identity for every physical row, including z=0.
There is no character-existence or nonprincipal hypothesis. -/
theorem row_weight_shift (η : Character) (m A z : O) (t v : ℝ) (I : Id) :
    rowWeight η m A z t I = idealHeight v I * rowWeight η m A z (t-v) I := by
  by_cases hI : I=0
  · subst I
    simp only [map_zero,mul_zero]
  have hn : (I.absNorm:ℂ)≠0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : (I.absNorm:ℂ)^(Complex.I*(t:ℂ)) =
      (I.absNorm:ℂ)^(Complex.I*(v:ℂ)) *
        (I.absNorm:ℂ)^(Complex.I*((t-v:ℝ):ℂ)) := by
    rw [←Complex.cpow_add _ _ hn]
    congr 1
    push_cast
    ring
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(I.absNorm:ℂ)^(Complex.I*(t:ℂ)) =
    heightPhase (I.absNorm:ℝ) v *
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*
        (I.absNorm:ℂ)^(Complex.I*((t-v:ℝ):ℂ)))
  rw [he]
  simp only [heightPhase,Complex.ofReal_natCast]
  ring

theorem selected_polynomial_shift (s : Source ι a b) (ha : 0<a)
    (seed F : Id) (η : Character) (m A : O) (t v : ℝ) (z : O) :
    selectedPolynomial s ha seed F η m A t z =
      residualPhase (s.X₁*s.X₂) s.d 1 v *
        selectedPolynomial (shiftSource s v) ha seed F η m A (t-v) z := by
  unfold selectedPolynomial
  rw [Finset.mul_sum]
  change (∑I∈sourceColumns s,selectedCoefficient s ha seed F I*rowWeight η m A z t I) = _
  apply Finset.sum_congr rfl
  intro I hI
  change (sourceCoefficient s ha seed I*selectedTwist F I)*rowWeight η m A z t I = _
  rw [row_weight_shift η m A z t v I]
  calc
    _ = (sourceCoefficient s ha seed I*idealHeight v I)*selectedTwist F I*
        rowWeight η m A z (t-v) I := by ring
    _ = _ := by
      rw [source_coefficient_shift s ha seed I v]
      change (_*sourceCoefficient (shiftSource s v) ha seed I)*selectedTwist F I*
        rowWeight η m A z (t-v) I = _
      unfold selectedCoefficient
      ring

theorem selected_polynomial_norm_shift (s : Source ι a b) (ha : 0<a)
    (seed F : Id) (η : Character) (m A : O) (t v : ℝ) (z : O) :
    ‖selectedPolynomial s ha seed F η m A t z‖ =
      ‖selectedPolynomial (shiftSource s v) ha seed F η m A (t-v) z‖ := by
  rw [selected_polynomial_shift s ha seed F η m A t v z,norm_mul,
    residual_phase_norm (s.X₁*s.X₂)
      (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂))
      s.d s.hd 1 one_ne_zero v,one_mul]

/-- The keep predicate is identical on the two sides and may depend on F. -/
theorem selected_energy_shift (s : Source ι a b) (ha : 0<a)
    (seed F : Id) (η : Character) (m A : O) (t v : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    selectedEnergy s ha seed F η m A t keep Φ K =
      selectedEnergy (shiftSource s v) ha seed F η m A (t-v) keep Φ K := by
  unfold selectedEnergy radialEnergy
  apply tsum_congr
  intro z
  split_ifs
  · rw [selected_polynomial_norm_shift s ha seed F η m A t v z]
  · rfl

/-- Equality in complex energy, not merely equality of its real part or
its norm. Thus it commutes with the original grouped selected sum. -/
theorem finite_energy_shift (s : Source ι a b) (ha : 0<a)
    (seed F : Id) (η : Character) (m A : O) (t v : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t (sourceColumns s) (selectedCoefficient s ha seed F) Φ K =
      finiteHeckeEnergy η m A (t-v) (sourceColumns (shiftSource s v))
        (selectedCoefficient (shiftSource s v) ha seed F) Φ K := by
  unfold finiteHeckeEnergy
  apply tsum_congr
  intro z
  change ((‖selectedPolynomial s ha seed F η m A t z‖^2:ℝ):ℂ)*_ =
    ((‖selectedPolynomial (shiftSource s v) ha seed F η m A (t-v) z‖^2:ℝ):ℂ)*_
  rw [selected_polynomial_norm_shift s ha seed F η m A t v z]

/-- The literal avoidance indicator commutes with height multiplication.
No support comparison between two cancelled column sums is used. -/
theorem source_coefficient_shift_avoid (s : Source ι a b) (ha : 0<a)
    (u seed I : Id) (v : ℝ) :
    sourceCoefficient (shiftSource (avoidSource s u) v) ha seed I =
      sourceCoefficient (avoidSource (shiftSource s v) u) ha seed I := by
  have hν : (fun i=>heightCoefficient (avoid u s.ν i) v) =
      avoid u (fun i=>heightCoefficient (s.ν i) v) := by
    funext i J
    by_cases h : J∣u
    · simp only [heightCoefficient,avoid,if_pos h,zero_mul]
    · simp only [heightCoefficient,avoid,if_neg h]
  dsimp only [sourceCoefficient,shiftSource,avoidSource]
  simp only [hν]

theorem finite_energy_shift_avoid (s : Source ι a b) (ha : 0<a)
    (u seed F : Id) (η : Character) (m A : O) (t v : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t (sourceColumns (avoidSource s u))
        (selectedCoefficient (avoidSource s u) ha seed F) Φ K =
      finiteHeckeEnergy η m A (t-v) (sourceColumns (avoidSource (shiftSource s v) u))
        (selectedCoefficient (avoidSource (shiftSource s v) u) ha seed F) Φ K := by
  rw [finite_energy_shift (avoidSource s u) ha seed F η m A t v Φ K]
  have hc : selectedCoefficient (shiftSource (avoidSource s u) v) ha seed F =
      selectedCoefficient (avoidSource (shiftSource s v) u) ha seed F := by
    funext I
    exact congrArg (fun z : ℂ=>z*selectedTwist F I)
      (source_coefficient_shift_avoid s ha u seed I v)
  rw [hc]
  rfl

/-- Every original complex weight and normalization can be kept verbatim.
In particular weight F may be groupedWeight F / selected padded scale. -/
theorem grouped_finite_energy_shift_avoid (s : Source ι a b) (ha : 0<a)
    (u seed : Id) (η : Character) (m A : O) (t v : ℝ)
    (Ds : Finset Id) (weight : Id→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑F∈Ds,weight F*finiteHeckeEnergy η m A t (sourceColumns (avoidSource s u))
      (selectedCoefficient (avoidSource s u) ha seed F) Φ K) =
    ∑F∈Ds,weight F*finiteHeckeEnergy η m A (t-v)
      (sourceColumns (avoidSource (shiftSource s v) u))
      (selectedCoefficient (avoidSource (shiftSource s v) u) ha seed F) Φ K := by
  apply Finset.sum_congr rfl
  intro F hF
  rw [finite_energy_shift_avoid s ha u seed F η m A t v Φ K]

def midpoint (t₀ tp : ℝ) : ℝ := (t₀+tp)/2
def heightTransfer (t₀ tp : ℝ) : ℝ := (tp-t₀)/2

theorem midpoint_equations (t₀ tp : ℝ) :
    t₀+heightTransfer t₀ tp=midpoint t₀ tp ∧
      tp-heightTransfer t₀ tp=midpoint t₀ tp := by
  constructor <;> unfold heightTransfer midpoint <;> ring

theorem midpoint_height_bound (s : Source ι a b) (t₀ tp V : ℝ) (hV : 0≤V) :
    height (midpoint t₀ tp) V (s.t₁+heightTransfer t₀ tp) (s.t₂+heightTransfer t₀ tp) ≤
      2*height t₀ V s.t₁ s.t₂*(1+|tp|) := by
  have hm : |midpoint t₀ tp|≤(|t₀|+|tp|)/2 := by
    unfold midpoint
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (abs_add_le t₀ tp) (by norm_num)
  have hv : |heightTransfer t₀ tp|≤(|tp|+|t₀|)/2 := by
    unfold heightTransfer
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le tp (-t₀)
  have h₁ := abs_add_le s.t₁ (heightTransfer t₀ tp)
  have h₂ := abs_add_le s.t₂ (heightTransfer t₀ tp)
  simp only [height,Real.norm_eq_abs]
  nlinarith [abs_nonneg t₀,abs_nonneg tp,abs_nonneg s.t₁,abs_nonneg s.t₂,
    mul_nonneg (show 0≤|t₀|+V+|s.t₁|+|s.t₂| by positivity) (abs_nonneg tp)]

section Canonical
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

theorem shifted_canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t₀ v : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t₀ R₀ s) :
    Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq (t₀+v) R₀ (shiftSource s v) := by
  obtain ⟨hS,hpool,hν,hW,hP⟩ := hs
  refine ⟨hS,hpool,?_,hW,hP⟩
  change (fun i=>heightCoefficient (s.ν i) v)=_
  rw [hν,canonical_height_all]

theorem midpoint_canonical (W : ℝ→ℂ) (Cap Lcap Z : ℝ) (η₀ : Character)
    (θ : ι→RayQuotient.Characters M Hray) (w σ freq : ι→ℝ) (t₀ tp : ℝ)
    (R₀ : ι→Finset Id) (s : Source ι a b)
    (hs : Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t₀ R₀ s) :
    Canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq (midpoint t₀ tp) R₀
      (shiftSource s (heightTransfer t₀ tp)) := by
  simpa only [(midpoint_equations t₀ tp).1] using
    shifted_canonical M Hray hHray W Cap Lcap Z η₀ θ w σ freq t₀
      (heightTransfer t₀ tp) R₀ s hs

/- Insert inside namespace MixedFirstReheight, after midpoint_canonical
   and before `end Canonical`. The base module is centrally checking;
   this fragment deliberately does not modify that file or any src file. -/

universe v
open ConcretePrimeRowBridge ActualEisensteinCubic RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional
open MixedFirstGeometricCaps MixedInnerExceptionalBlock ReferencePrimeEnclosure
open MixedFirstUniformLossBudget MixedFirstChosenEnergy

/-- The actual chosen first energy with independent canonical slot height
t0 and physical row height tp. Every scalar hypothesis, selected weight,
source normalization, and geometric gate is the original ChosenEnergy
hypothesis. The midpoint transfer changes only explicit height costs. -/
theorem uniform_chosen_independent_energy
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b B Lslot Lcap Cap BR BH Bη lo hi cstar Kslot Bseed εfinal rho : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hB : 1≤B) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBη : 0≤Bη) (hCapb : b≤Cap) (hBcap : B≤Lcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hcstar : 0<cstar) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hεfinal : 0<εfinal) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed εfinal rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset ι,
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s→
      s.d=(1,1)→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      Z^(-B)≤s.L→s.X₁≤Z^B→s.X₂≤Z^B→s.Y₁≤Z^B→s.Y₂≤Z^B→(∏i,s.P i)≤Z^B→
    ∀cover : OriginalEnclosure s,∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→1≤sharpSupport s→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀u : Id,u∣s.R→∀(α : Type v) [Fintype α],∀q : MixedSupplierFourthRow.Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
      cstar*Z^(referenceExponent R P S d)≤s.L→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    let A := sourceControl control s.W₁*sourceControl control s.W₂
    let H := height t₀ V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈MixedSupplierPositive.selectedProducts q,
          ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal := by
  dsimp only
  obtain ⟨J,control,hbase⟩ := uniform_chosen_first_energy (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b B Lslot Lcap Cap BR BH Bη lo hi cstar Kslot Bseed εfinal rho
    hWs hW ha haUpper hb hB hLslot hLcap hCap hBR hBH hBη hCapb hBcap
    hβ hcstar hKslot hBseed hεfinal hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hη₀
  refine ⟨C*2^J,mul_pos hC (pow_pos (by norm_num) J),?_⟩
  filter_upwards [hbase] with Z hbaseZ
  refine ⟨hbaseZ.1,?_⟩
  intro T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqν hqW
    hWcap hWinv hqvolume hR0 hmixed hnative hlength Dseed hDseed hDcap
  let sh := shiftSource s (heightTransfer t₀ tp)
  have hc : Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i : T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      (midpoint t₀ tp) (fun i=>R₀ i.val) sh :=
    midpoint_canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i : T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ tp (fun i=>R₀ i.val) s hcanonical
  have he := hbaseZ.2 T θ w σ freq (midpoint t₀ tp) V R₀ hw hwL hσ hσhi hV hfreq hR₀
    sh hc hunit hMs hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP
    cover η hη K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α q
    hα hqP hqpool hqν hqW hWcap hWinv hqvolume hR0 hmixed hnative hlength
    Dseed hDseed hDcap
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := height t₀ V s.t₁ s.t₂
  let Hmid := height (midpoint t₀ tp) V (s.t₁+heightTransfer t₀ tp) (s.t₂+heightTransfer t₀ tp)
  let Eold : ℂ := ∑F∈MixedSupplierPositive.selectedProducts q,
    ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
      finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
        (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K
  let Enew : ℂ := ∑F∈MixedSupplierPositive.selectedProducts q,
    ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
      finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 (midpoint t₀ tp)
        (sourceColumns (avoidSource sh u)) (selectedCoefficient (avoidSource sh u) ha 1 F) Φ K
  have heq : Eold=Enew := by
    simpa only [Eold,Enew,sh,(midpoint_equations t₀ tp).2] using
      grouped_finite_energy_shift_avoid s ha u 1 η (fixedBadMask*idealGenerator s.R) 1
        tp (heightTransfer t₀ tp) (MixedSupplierPositive.selectedProducts q)
        (fun F=>((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)) Φ K
  change ((Dseed.absNorm:ℝ)^(budgetStep B Bseed εfinal rho)*Z^(budgetStep B Bseed εfinal rho))*
      (‖Enew‖/sourceVolume s)≤C*Kslot^(2*N)*A^2*Hmid^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal at he
  rw [←heq] at he
  apply he.trans
  have hmid : 0≤Hmid := by
    dsimp only [Hmid,height]
    positivity
  have hpow : Hmid^J≤(2*H*(1+|tp|))^J :=
    pow_le_pow_left₀ hmid (midpoint_height_bound s t₀ tp V hV) J
  let Ap := C*Kslot^(2*N)*A^2*((η.modulus.absNorm:ℝ)*K)*Z^εfinal
  have hAp : 0≤Ap := by
    dsimp only [Ap]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le
      (pow_nonneg (zero_le_one.trans hKslot) _)) (sq_nonneg A))
      (mul_nonneg (Nat.cast_nonneg _) hK.le))
      (Real.rpow_nonneg (zero_le_one.trans hbaseZ.1.le) _)
  calc
    _ = Ap*Hmid^J := by dsimp only [Ap];ring
    _ ≤ Ap*(2*H*(1+|tp|))^J := mul_le_mul_of_nonneg_left hpow hAp
    _ = _ := by simp only [mul_pow];dsimp only [Ap,A,H];ring

end Canonical
end
end Candidate.FourthPower.MixedFirstReheight
