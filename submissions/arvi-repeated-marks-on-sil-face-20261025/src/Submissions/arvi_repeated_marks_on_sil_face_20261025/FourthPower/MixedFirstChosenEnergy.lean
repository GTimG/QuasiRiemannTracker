/- Copyright (c) 2026 Sil. Apache-2.0.
Actual grouped energy with chosen losses and actual logarithmic geometry.
No Gates, SourceGeometry or energy estimate is an input. Parent checks Lean.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstUniformEnergy
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstUniformLossBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstChosenEnergy
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge ActualEisensteinCubic RayFourExpansion
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
open MixedFirstActualNonexceptional MixedFirstExceptionalApplication
open MixedFirstAvoidance MixedFirstPhysicalApplication MixedFirstGeometricCaps
open MixedFirstPaidCosts MixedFirstCutoffs MixedFirstProfileEnvelope
open MixedFirstUniformEnergy MixedFirstUniformLossBudget
open MixedCompletedRows ReferencePrimeEnclosure
open QRH.Record1252270103KernelMass (pairNorm ideal_norm_one_le)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι]

/-- The deterministic midpoint already used in the paper and in
reference_interval_nonempty. Equality belongs to the uncentered case. -/
def referenceExponent (R P S d : ℝ) : ℝ :=
  if P+S≤5*R/6-7*d/3 then 0
  else (MixedLedger.lower R P S d+MixedLedger.upper R P S d)/2

theorem reference_exponent_choice (R P S d : ℝ) (h : P+2*S+4*d<R) :
    ReferenceChoice R P S d (referenceExponent R P S d) := by
  unfold referenceExponent
  split_ifs with hc
  · exact Or.inl ⟨rfl,hc⟩
  · have hw := MixedLedger.reference_interval_width R P S d
    refine Or.inr ⟨lt_of_not_ge hc,?_,?_⟩ <;> linarith

/-- The reference may pay its fixed conductor by d+omega while the
actual first energy keeps d. The midpoint has a common original reserve;
omega=budgetStep and deltaRef=budgetStep/2 fit these two inequalities. -/
theorem reference_exponent_margins (R P S d rho omega deltaRef : ℝ)
    (hrho : 0<rho) (hS : 0≤S) (hd : 0≤d)
    (hcap : P+2*S+4*d≤R-rho) (hcenter : 5*R/6-7*d/3<P+S)
    (homega : omega≤rho/100) (hdelta : deltaRef≤rho/200) :
    let l := referenceExponent R P S d
    0<l ∧ l<P/2 ∧
      l+(R+(d+omega))/2+S+2*deltaRef≤(4/5)*R ∧
      R+(d+omega)+2*l-P+S+2*deltaRef≤R/2 := by
  have hmix : P+2*S+4*d<R := by linarith
  have href := reference_exponent_choice R P S d hmix
  have hlower : MixedLedger.lower R P S d<referenceExponent R P S d := by
    rcases href with ⟨_,hc⟩|⟨_,hl,_⟩
    · linarith
    · exact hl
  have hupper : referenceExponent R P S d<MixedLedger.upper R P S d := by
    rcases href with ⟨_,hc⟩|⟨_,_,hu⟩
    · linarith
    · exact hu
  have hg := MixedLedger.reference_gate hS hd hmix (by linarith) hlower hupper
  dsimp only
  refine ⟨hg.1,hg.2.1,?_,?_⟩ <;>
    simp only [referenceExponent,if_neg (not_le.mpr hcenter)] <;>
    dsimp only [MixedLedger.lower,MixedLedger.upper] <;> linarith

theorem fixed_presentation_one_le : 1≤fixedPresentationCost := by
  have h₁ := ideal_norm_one_le (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero)
  have h₂ : (1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) := ideal_norm_one_le (by simp)
  unfold fixedPresentationCost
  nlinarith

/-- This is the actual width, including the fixed presentation factor.
It is not logb(Neta*K) with that factor silently discarded. -/
theorem input_width_power (η : Character) (K Z : ℝ) (hK : 0<K) (hZ : 1<Z) :
    Z^(inputWidth η K Z)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*K := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hη : 0<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
  unfold inputWidth
  rw [Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz hZ.ne' hK,Real.rpow_logb hz hZ.ne' hη,
    Real.rpow_logb hz hZ.ne' fixedPresentationCost_pos]
  ring

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Actual unit-prefix, live-seed-one energy, uniformly over every live
subset. Numeric exponents are the actual logarithms of total ordinary
volume and selected volume, and the actual sum of live marked widths.

The remaining length inequality is literal: the source must have the
chosen reference length. allocatedReference supplies it in the centered
branch; a short original rectangle is handled by the separate reference
supplier, not by assuming this inequality for an arbitrary source.

The full original seed norm is only an outside reconstruction cost here.
Its subpower and one reference loss are paid explicitly on the left.
All constants precede T, that seed, and every original profile/height.
-/
theorem uniform_chosen_first_energy
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
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source T a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t (fun i=>R₀ i.val) s→
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
    let H := height t V s.t₁ s.t₂
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      (‖∑F∈MixedSupplierPositive.selectedProducts q,
          ((MixedSupplierPositive.groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
          finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 t
            (sourceColumns (avoidSource s u)) (selectedCoefficient (avoidSource s u) ha 1 F) Φ K‖/
          sourceVolume s)≤
      C*Kslot^(2*N)*A^2*H^J*((η.modulus.absNorm:ℝ)*K)*Z^εfinal := by
  dsimp only
  let step := budgetStep B Bseed εfinal rho
  let h := physicalStep B Bseed εfinal rho
  let B0 := sourceExponent B
  let Mcap := 19*B0+Bη+6
  have hbud := chosen_loss_budgets B Bseed εfinal rho hB hBseed hεfinal hrho
  dsimp only at hbud
  have hstep : 0<step := hbud.1
  have hh : 0<h := hbud.2.1
  have hh1 : h≤1 := by have hhsmall := hbud.2.2.2.1;change h≤1/100 at hhsmall;linarith
  have hgap : (7/10:ℝ)+2*h<1 := hbud.2.2.2.2.2.1
  have hB0 : 1≤B0 := by dsimp only [B0,sourceExponent];linarith
  have hMcap0 : 0<Mcap := by dsimp only [Mcap];linarith
  have hMcap : geometryExponent B0 h+(Bη+B0+h)+B0+h≤Mcap := by
    dsimp only [geometryExponent,secondExponent,Mcap]
    linarith
  obtain ⟨J,control,henergy⟩ := uniform_grouped_first_energy_subsets (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Mcap B Lslot Lcap Cap BR BH Bη h h lo hi h h h
    (2*B0+1) step step cstar Kslot hWs hW ha haUpper hb hMcap0 hB hLslot hLcap hCap
    hBR hBH hCapb hBcap hh hh hgap hh hh hh hMcap hβ hstep hstep hcstar hKslot
    Q hQt hQ72 hQM
  have hgates := uniform_chosen_gates.{v} N B Bseed εfinal rho hB hBseed hεfinal hrho
  have hsharp := eventually_sharp_support.{u} N b 1 (by norm_num)
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C0,hC0,henergy⟩ := henergy η₀ hη₀
  refine ⟨3*fixedPresentationCost*C0,
    mul_pos (mul_pos (by norm_num) fixedPresentationCost_pos) hC0,?_⟩
  filter_upwards [henergy,hgates,hsharp] with Z henergyZ hgatesZ hsharpZ
  refine ⟨henergyZ.1,?_⟩
  intro T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical hunit hMs
    hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α instα q hα hqP hqpool hqν hqW
    hWcap hWinv hqvolume hR0 hmixed hnative hlength Dseed hDseed hDcap
  let R := inputWidth η K Z
  let P := Real.logb Z s.T
  let S := ∑i : T,w i.val
  let d := Real.logb Z (MixedSelectedVolume.volume q)
  have hZ : 1<Z := henergyZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  have hS : 0≤S := Finset.sum_nonneg (fun i _=>hw i.val)
  have hd : 0≤d := Real.logb_nonneg hZ hqvolume
  have hmix : P+2*S+4*d<R := by linarith
  have hreference := reference_exponent_choice R P S d hmix
  have hqvolumePos : 0<MixedSelectedVolume.volume q := zero_lt_one.trans_le hqvolume
  have hqpower : MixedSelectedVolume.volume q=Z^d :=
    (Real.rpow_logb hz hZ.ne' hqvolumePos).symm
  let p := chosenParameters B0 B0 B0 step (normExponent B B h) R P S d
    (referenceExponent R P S d) cstar Z K 0 (MixedSelectedVolume.scale q)
  have hp : Gates p := hgatesZ.2 R P S d (referenceExponent R P S d) cstar
    hS hd hcstar hmix hnative hreference α q hα hqP hqpower K 0 hK
  have hcardT : Fintype.card T≤N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans (by simpa using hcard)
  have hvolcap := (source_volume_caps s Z B hZ hmin hX₁ hX₂ hP).1
  have hpair : pairNorm s.d=1 := by simp only [hunit,pairNorm,map_one,Nat.cast_one,mul_one]
  have hxcap : sharpSupport s≤Z^B0 := by
    have hhcap := hsharpZ.2 T a s hcardT (3*B) hvolcap
    simpa only [hpair,div_one,B0,sourceExponent] using hhcap
  have hprod : (∏i : T,s.P i)=Z^S := by
    rw [hcanonical.2.2.2.2,←Real.rpow_sum_of_pos hz]
  have hvol : Real.logb Z (sourceVolume s)=P+S := by
    unfold sourceVolume
    rw [s.hpX,hprod,Real.logb_mul s.total_pos.ne' (Real.rpow_pos_of_pos hz S).ne',
      Real.logb_rpow hz hZ.ne']
  have hg : SourceGeometry p s η (fun i=>w i.val) := {
    volume := hvol.le
    width := le_refl _
    length := hlength
    support := hxcap
    slots := le_refl _ }
  have he := henergyZ.2 T θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreqs hR₀ s hcanonical
    hunit hMs hR hHholes hholes hHR hFhole hmin hX₁ hX₂ hY₁ hY₂ hP cover η hη
    K hK hKcap hKinv hX χ₀ msecond hm hml hm2 u hu α q hα hqP hqpool hqν hqW
    hWcap hWinv R P S d (referenceExponent R P S d) cstar h (3*h) step B0 (le_refl _) hp hg
  have hηone : (1:ℝ)≤(η.modulus.absNorm:ℝ) := ideal_norm_one_le η.modulus_ne_bot
  have hwidth : (η.modulus.absNorm:ℝ)*K≤Z^R := by
    change (η.modulus.absNorm:ℝ)*K≤Z^(inputWidth η K Z)
    rw [input_width_power η K Z hK hZ]
    have hh := mul_le_mul_of_nonneg_right fixed_presentation_one_le
      (mul_nonneg (zero_le_one.trans hηone) hK.le)
    simpa only [one_mul,mul_assoc] using hh
  have hNs : 0<(Dseed.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hDseed)
  have hpay := normalized_grouped_rhs_paid B Bseed εfinal rho Z R (η.modulus.absNorm:ℝ) K
    (Dseed.absNorm:ℝ) 1 hB hBseed hεfinal hrho hZ.le hR0 hηone hK.le hwidth hNs hDcap
    zero_lt_one
  simp only [one_mul] at hpay
  have hpay' := (div_le_div_iff_of_pos_right hNs).mp hpay
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := height t V s.t₁ s.t₂
  let Ap := C0*Kslot^(2*N)*A^2*H^J
  have hH : 1≤H := by
    dsimp only [H,height]
    linarith [abs_nonneg t,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hAp : 0≤Ap := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC0.le
      (pow_nonneg (zero_le_one.trans hKslot) _)) (sq_nonneg A))
      (pow_nonneg (zero_le_one.trans hH) _)
  have hfac : 0≤(Dseed.absNorm:ℝ)^step*Z^step :=
    mul_nonneg (Real.rpow_nonneg hNs.le _) (Real.rpow_nonneg hz.le _)
  dsimp only at he hpay' ⊢
  have he' := mul_le_mul_of_nonneg_left he hfac
  have hpay'' := mul_le_mul_of_nonneg_left hpay' hAp
  calc
    _≤Ap*((Dseed.absNorm:ℝ)^step*Z^step)*
        ((η.modulus.absNorm:ℝ)*K*Z^(step+5*(tailExponent B0 h h)*h+step+
          (tailExponent B0 h h)*step)+K*Z^(B0*h+(tailExponent B0 h h)*step)+
          Z^(-(2*B0+1)+(tailExponent B0 h h)*step)) := by
      convert he' using 1 <;> (try dsimp only [Ap,A,H]) <;> ring
    _≤Ap*(3*Z^(R+εfinal)) := by
      convert hpay'' using 1 <;> ring
    _=_ := by
      change Ap*(3*Z^(inputWidth η K Z+εfinal))=_
      rw [Real.rpow_add hz,input_width_power η K Z hK hZ]
      dsimp only [Ap,A,H]
      ring

end
end Candidate.FourthPower.MixedFirstChosenEnergy
