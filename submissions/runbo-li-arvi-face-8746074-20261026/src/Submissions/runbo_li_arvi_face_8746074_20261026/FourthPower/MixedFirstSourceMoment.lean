/- Copyright (c) 2026 Sil. Apache-2.0.
The whole original unit-prefix selected source. Constants precede all
live subsets and original source data; the eligible rows may depend on
the selected product. Parent alone runs the pinned Lean checker.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstActualReference
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstReheight
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstSourceGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstSourceMoment
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge ConcreteTraceCRT ActualEisensteinCubic RayFourExpansion
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentOriginalRadialComparison CenteredMomentEnergyCapacityRemoval
open CenteredMomentFiniteProfileExceptional CenteredMomentAbsoluteEnergy
open CenteredMomentSourceRow CenteredMomentUncenteredTerminal CenteredExceptionalProfile
open MixedFirstReferenceEnergy
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstPhysicalApplication MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstReferenceDispatch MixedFirstProfileEnvelope
open MixedFirstAvoidance MixedSupplierSource MixedSupplierFourthRow MixedSupplierPositive
open MixedFirstGeometricCaps MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstChosenReferenceSource MixedFirstActualReference MixedFirstReheight
open MixedFirstSourceGeometry MixedCanonicalSource ReferencePrimeEnclosure
open MixedFirstActualNonexceptional MixedFirstReferenceChoice MixedFirstCutoffs
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Redundant marked avoidance is removed before applying the canonical
energy endpoint. This is equality of the actual column coefficients,
not a false implication between supports of differently masked sums. -/
theorem source_coefficient_avoid_dvd (s : Source ι a b) (ha : 0<a)
    (u : Id) (hu : u∣s.R) (seed I : Id) :
    sourceCoefficient (avoidSource s u) ha seed I=sourceCoefficient s ha seed I := by
  unfold sourceCoefficient MixedHeightEnergy.originalColumn
  unfold CenteredMomentSourceMass.finiteColumnCoefficient
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [avoidSource]
  rw [profile_avoid s.R u seed hu]
  intro i
  exact s.hp i _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 (Sum.inl i))

theorem selected_avoid_dvd (s : Source ι a b) (ha : 0<a)
    (u : Id) (hu : u∣s.R) (seed F : Id) :
    selectedCoefficient (avoidSource s u) ha seed F=selectedCoefficient s ha seed F := by
  funext I
  exact congrArg (·*selectedTwist F I) (source_coefficient_avoid_dvd s ha u hu seed I)

/-- The selected weighted average, with its original source-volume
normalization and its literal F-dependent keep. -/
def groupedMoment {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    selectedEnergy s ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K)/sourceVolume s

theorem grouped_moment_nonneg {α : Type v} [Fintype α] (q : Data α)
    (hP : ∀i,0<q.P i) (s : Source ι a b) (ha : 0<a) (η : Character)
    (tp : ℝ) (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀x,0≤(Φ x).re) : 0≤groupedMoment q s ha η tp keep Φ K := by
  apply div_nonneg _ (sourceVolume_pos s).le
  apply Finset.sum_nonneg
  intro F hF
  exact mul_nonneg
    (div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hP).le)
    (selected_energy_nonneg s ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K
      (fun z=>hΦ _))

/-- The complete canonical energy consumes the same grouped average.
Only the centered positive keep is enlarged; the redundant whole-source
mask and u=1 avoidance are exact equalities. -/
theorem grouped_moment_le_chosen {α : Type v} [Fintype α] (q : Data α)
    (hP : ∀i,0<q.P i) (s : Source ι a b) (ha : 0<a) (η : Character)
    (tp : ℝ) (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re) :
    groupedMoment q s ha η tp keep Φ K≤
      ‖∑F∈selectedProducts q,((groupedWeight q F/MixedSelectedVolume.scale q:ℝ):ℂ)*
        finiteHeckeEnergy η (fixedBadMask*idealGenerator s.R) 1 tp
          (sourceColumns (avoidSource s 1))
          (selectedCoefficient (avoidSource s 1) ha 1 F) Φ K‖/sourceVolume s := by
  have he := grouped_selected_kept_positive_le_norm q hP (avoidSource s 1) ha 1 η
    (fixedBadMask*idealGenerator s.R) tp keep Φ K 2 hK hΦs hΦ
  have hpoint (F : Id) :
      selectedEnergy (avoidSource s 1) ha 1 F η (fixedBadMask*idealGenerator s.R) 1 tp
        (keep F) Φ K=selectedEnergy s ha 1 F η fixedBadMask 1 tp (keep F) Φ K := by
    have hc := selected_avoid_dvd s ha 1 (one_dvd _) 1 F
    have hp : selectedPolynomial (avoidSource s 1) ha 1 F η
        (fixedBadMask*idealGenerator s.R) 1 tp =
        selectedPolynomial s ha 1 F η (fixedBadMask*idealGenerator s.R) 1 tp := by
      funext z
      unfold selectedPolynomial
      change (∑ I ∈ sourceColumns s, selectedCoefficient (avoidSource s 1) ha 1 F I *
        CenteredMomentHeckeExpansion.rowWeight η (fixedBadMask*idealGenerator s.R) 1 z tp I) = _
      rw [hc]
    exact (congrArg (fun f => radialEnergy f (keep F) Φ K) hp).trans
      (selected_energy_mask s ha 1 F s.R (dvd_refl _) η 1 tp (keep F) Φ K)
  simp_rw [hpoint] at he
  unfold groupedMoment
  rw [Finset.sum_coe_sort (selectedProducts q) (fun F : Id =>
    (groupedWeight q F/MixedSelectedVolume.scale q)*selectedEnergy s ha 1 F η fixedBadMask 1 tp (keep F) Φ K)]
  exact he

/-- Exact normalization on the original uncentered row, including its
literal selected character and physical height. -/
theorem uncentered_energy_eq (s : Source ι a b) (ha : 0<a)
    (hd : s.d=(1,1)) (hG : s.G=1)
    (hY : s.Y₁≤comparisonScale b ∨ s.Y₂≤comparisonScale b)
    (η : Character) (F : Id) (hF : Supported F) (tp : ℝ)
    (keep : O→Prop) (hkeep : ∀z,keep z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    selectedEnergy s ha 1 F η fixedBadMask 1 tp keep Φ K/sourceVolume s=
      radialEnergy (fun z=>heightRectangle s ha
        (selectedCharacterAt η fixedBadMask F fixedBadMask_ne_zero hF
          (dvd_mul_right _ _) (dvd_mul_left _ _) z) tp s.X₁ s.X₂) keep Φ K := by
  unfold selectedEnergy sourceVolume
  rw [←radial_normalization (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i=>zero_lt_one.trans_le (s.hP i))]
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · have hn := hkeep z hz
    let r := Classical.choice (selected_character_exists η fixedBadMask F z
      fixedBadMask_ne_zero hF hn (dvd_mul_right _ _) (dvd_mul_left _ _))
    have hc : selectedCharacterAt η fixedBadMask F fixedBadMask_ne_zero hF
        (dvd_mul_right _ _) (dvd_mul_left _ _) z=r.character := by
      rw [selectedCharacterAt,dif_pos hn]
    simp only [if_pos hz,hc,selected_uncentered s ha hd hG hY η fixedBadMask F z
      (dvd_mul_right _ _) (dvd_mul_left _ _) r tp]
  · simp only [if_neg hz]

theorem grouped_uncentered_eq {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (hd : s.d=(1,1)) (hG : s.G=1)
    (hY : s.Y₁≤comparisonScale b ∨ s.Y₂≤comparisonScale b)
    (η : Character) (tp : ℝ) (keep : Id→O→Prop)
    (hkeep : ∀F∈selectedProducts q,∀z,keep F z→z≠0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    groupedMoment q s ha η tp keep Φ K=
      ∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        radialEnergy (fun z=>heightRectangle s ha
          (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
            (selected_products_supported q F.val F.property)
            (dvd_mul_right _ _) (dvd_mul_left _ _) z) tp s.X₁ s.X₂) (keep F.val) Φ K := by
  unfold groupedMoment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro F hF
  rw [mul_div_assoc,uncentered_energy_eq s ha hd hG hY η F.val
    (selected_products_supported q F.val F.property) tp (keep F.val)
    (hkeep F.val F.property) Φ K]

private theorem control_pair_mono (A B : Finset (ℕ×ℕ)) (hAB : A⊆B)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) :
    (sourceControl A W₁*sourceControl A W₂)^2≤
      (sourceControl B W₁*sourceControl B W₂)^2 := by
  have hm (W : 𝓢(ℝ,ℂ)) : sourceControl A W≤sourceControl B W :=
    Seminorm.le_def.mp (Finset.sup_mono hAB) W
  exact pow_le_pow_left₀ (mul_nonneg (sourceControl_nonneg A W₁) (sourceControl_nonneg A W₂))
    (mul_le_mul (hm W₁) (hm W₂) (sourceControl_nonneg A W₂) (sourceControl_nonneg B W₁)) 2

private theorem original_height_bound (t₀ tp V t₁ t₂ : ℝ) (hV : 0≤V) :
    height tp V t₁ t₂≤height t₀ V t₁ t₂*(1+|tp|) := by
  dsimp only [height]
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg t₀,abs_nonneg tp,abs_nonneg t₁,abs_nonneg t₂,
    mul_nonneg (show 0≤|t₀|+V+|t₁|+|t₂| by positivity) (abs_nonneg tp)]

/-- The reference theorem already includes the selected-fiber loss.
Only the stated seed cost and the retained Z^step remain to pay. -/
theorem reference_seed_budget (B Bseed ε rho : ℝ)
    (hB : 1≤B) (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho) :
    (Bseed+3/2)*budgetStep B Bseed ε rho≤ε := by
  let step := budgetStep B Bseed ε rho
  let den := budgetDenominator B Bseed
  have hs : 0<step := budget_step_pos B Bseed ε rho hB hBseed hε hrho
  have hd : Bseed+2≤den := by
    dsimp only [den,budgetDenominator,tailCap,MixedFirstCutoffs.sourceExponent]
    linarith
  have hd0 : 0<den := by linarith
  have hpay : step*(100*den)≤ε :=
    ((le_div_iff₀ (by positivity : 0<100*den)).mp
      (show step≤min 1 ε/(100*den) from min_le_right _ _)).trans (min_le_right _ _)
  change (Bseed+3/2)*step≤ε
  nlinarith

private theorem radial_split (f g h : O→ℂ) (keep : O→Prop)
    (he : ∀z,keep z→f z=g z+h z) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re) :
    radialEnergy f keep Φ K≤2*(radialEnergy g keep Φ K+radialEnergy h keep Φ K) := by
  have hf := compact_radial_summable f keep Φ K 2 hK hΦs
  have hg := compact_radial_summable g keep Φ K 2 hK hΦs
  have hh := compact_radial_summable h keep Φ K 2 hK hΦs
  unfold radialEnergy
  calc
    _≤∑'z:O,2*((if keep z then ‖g z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)+
      (if keep z then ‖h z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)) := by
      apply hf.tsum_le_tsum _ ((hg.add hh).mul_left 2)
      intro z
      by_cases hz : keep z
      · have hn := norm_add_le (g z) (h z)
        have hsq : ‖f z‖^2≤2*(‖g z‖^2+‖h z‖^2) := by
          rw [he z hz]
          nlinarith [norm_nonneg (g z),norm_nonneg (h z),norm_nonneg (g z+h z),
            sq_nonneg (‖g z‖-‖h z‖)]
        simp only [if_pos hz]
        convert mul_le_mul_of_nonneg_right hsq (hΦ _) using 1 <;> ring
      · simp only [if_neg hz,zero_add,mul_zero,le_refl]
    _=_ := by rw [tsum_mul_left,hg.tsum_add hh]

private theorem normalized_energy (s : Source ι a b) (ha : 0<a)
    (F : Id) (η : Character) (tp : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (fun z=>normalization (s.X₁*s.X₂) s.P*
      selectedPolynomial s ha 1 F η fixedBadMask 1 tp z) keep Φ K=
      selectedEnergy s ha 1 F η fixedBadMask 1 tp keep Φ K/sourceVolume s :=
  radial_normalization (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i=>zero_lt_one.trans_le (s.hP i)) _ keep Φ K

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 1600000 in
/-- Whole original uncentered source moment, uniformly before every
live subset, source, selected family, height and original ideal seed.
The source itself may have arbitrarily short original reference lengths.
Tiny original factors vanish exactly; short originals use the actual
reference theorem; otherwise the chosen reference is constructed inside
this proof. There is no reference-length or energy estimate hypothesis.

The literal F-dependent nonprincipal restriction survives in both
reference uses. Only the positive chosen centered energy is enlarged.
The additional seed reconstruction reserve is displayed on the left.
-/
theorem uniform_source_moment
    (Φ : 𝓢(ℝ,ℂ)) (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) (hΦ : ∀x,0≤(Φ x).re)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step := budgetStep B Bseed ε rho
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
      s.d=(1,1)→s.G=1→(∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i : T,∀P∈s.H,P.val∈R₀ i.val)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→
      (s.Y₁≤comparisonScale b ∨ s.Y₂≤comparisonScale b)→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R := inputWidth η K Z
    let P := Real.logb Z s.T
    let S := ∑i : T,w i.val
    let d := Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀Dseed : Id,Dseed≠0→(Dseed.absNorm:ℝ)≤Z^Bseed→
    ((Dseed.absNorm:ℝ)^step*Z^step)*groupedMoment q s ha η tp keep Φ K≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε := by
  dsimp only
  let step := budgetStep B Bseed ε rho
  let Binput := Bη+B+1
  let BRref := referenceWidth Binput B Lcap BR0 BH
  have hB1 : 1≤B := by linarith
  have hB0 : 0≤B := zero_le_one.trans hB1
  have hLcap0 : 0≤Lcap := hB0.trans hBcap
  have hinput0 : 0≤Binput := by dsimp only [Binput];positivity
  have hLc : 2*Lorig≤Lcap := by linarith
  have hCapb : b≤Cap := by
    have hc := comparisonScale_pos b
    have hc1 : comparisonScale b≤1 :=
      (MixedFirstReferenceChoice.comparison_scale_le_half b).trans (by norm_num)
    exact ((le_div_iff₀ hc).mpr (mul_le_of_le_one_right (zero_le_one.trans hb) hc1)).trans hCapc
  have hstep : 0<step := budget_step_pos B Bseed ε rho hB1 hBseed hε hrho
  have hwidth := reference_width_bounds Binput B Lcap BR0 BH hinput0 hB0 hLcap0 hBR0 hBH
  have hBRref : 0≤BRref := hwidth.1
  obtain ⟨Jc,Sc,hchosen⟩ := uniform_chosen_independent_energy (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b B Lslot Lcap Cap BR0 BH Bη lo hi (comparisonScale b)
    Kslot Bseed ε rho hWs hW ha haUpper hb hB1 hLslot hLcap hCap hBR0 hBH hBη
    hCapb hBcap hβ (comparisonScale_pos b) hKslot hBseed hε hrho Q hQt hQ72 hQM
  obtain ⟨Jr,Sr,Cr,hCr,h00,href⟩ := uniform_actual_reference_weighted (ι:=ι)
    N hcard (step/2) a b BRref B B rho Kslot (half_pos hstep) ha (zero_le_one.trans hb)
    hBRref hB0 hB0 hrho hKslot
  let J := Jc+Jr
  let control := Sc∪Sr
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨Cc,hCc,hchosen⟩ := hchosen η₀ hη₀
  let C := 2*(Cc+radialControl Φ*Cr)
  have hC : 0<C := by
    have hc := radial_control_nonneg Φ
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  have hadmission := eventually_reference_admission.{u} N b Cap B Binput Lcap BR0 BH B rho
    (zero_le_one.trans hb) (by linarith) hB0 hinput0 hLcap0 hBR0 hBH hB0 hrho.le
  have hpowers := eventually_chosen_power_caps.{u} b Lorig B hLorig hB
  filter_upwards [hchosen,href,hadmission,hpowers,eventually_ge_atTop fixedPresentationCost]
    with Z hcZ hrZ hadZ hpZ hfixed
  have hZ : 1<Z := hcZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hd hG hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
  let R := inputWidth η K Z
  let P := Real.logb Z s.T
  let S := ∑i : T,w i.val
  let d := Real.logb Z (MixedSelectedVolume.volume q)
  let l := referenceExponent R P S d
  let H := height t₀ V s.t₁ s.t₂
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let cost := Kslot^(2*N)*A^2*H^J*(1+|tp|)^J*((η.modulus.absNorm:ℝ)*K)*Z^ε
  let reserve := (Dseed.absNorm:ℝ)^step*Z^step
  have hreserve : 0≤reserve := by dsimp only [reserve];positivity
  have hH : 1≤H := by
    dsimp only [H,height]
    linarith [abs_nonneg t₀,norm_nonneg s.t₁,norm_nonneg s.t₂]
  have hH0 : 0≤H := zero_le_one.trans hH
  have hKslot0 : 0≤Kslot := zero_le_one.trans hKslot
  have htp : 1≤1+|tp| := le_add_of_nonneg_right (abs_nonneg _)
  have hcost : 0≤cost := by dsimp only [cost];positivity
  have hcardT : Fintype.card T≤N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ T)).trans (by simpa using hcard)
  have hproduct := canonical_product M Hray hHray Wslot Cap Lcap Z η₀
    (fun i:T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) t₀
    (fun i=>R₀ i.val) s hcanonical N Lslot B hZ hcardT hLslot
    (fun i=>hw i.val) (fun i=>hwL i.val) hslots
  have hS : 0≤S := hproduct.2.1
  have hprod : (∏i,s.P i)≤Z^B := hproduct.2.2
  have hprodS : (∏i,s.P i)≤Z^S := hproduct.1.le
  have hqvolumeCap : MixedSelectedVolume.volume q≤Z^B := by
    apply le_trans _ hWcap
    change MixedSelectedVolume.volume q≤MixedSelectedVolume.padding q*MixedSelectedVolume.volume q
    exact le_mul_of_one_le_left (zero_le_one.trans hqvolume)
      (one_le_pow₀ (by norm_num))
  have hRcap : R≤BRref := by
    have hηpos : 0<(η.modulus.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)
    have hn := Real.logb_le_logb_of_le hZ hηpos hη
    have hk := Real.logb_le_logb_of_le hZ hK hKcap
    have hf := Real.logb_le_logb_of_le hZ fixedPresentationCost_pos
      (show fixedPresentationCost≤Z^(1:ℝ) by simpa only [Real.rpow_one] using hfixed)
    rw [Real.logb_rpow hz hZ.ne'] at hn hk
    rw [Real.logb_rpow hz hZ.ne'] at hf
    have hRI : R≤Binput := by dsimp only [R,inputWidth,Binput];linarith
    exact hRI.trans hwidth.2.1
  have hmix : P+2*S+4*d<R := by linarith
  have hX₁B : s.X₁≤Z^B := hX₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hX₂B : s.X₂≤Z^B := hX₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hSc : Sc⊆control := Finset.subset_union_left
  have hSr : Sr⊆control := Finset.subset_union_right
  have hJc : Jc≤J := Nat.le_add_right _ _
  have hJr : Jr≤J := Nat.le_add_left _ _
  have hpay : reserve*Z^(step/2)≤Z^ε := by
    have hn : (Dseed.absNorm:ℝ)^step≤Z^(Bseed*step) := by
      calc
        _≤(Z^Bseed)^step := Real.rpow_le_rpow (Nat.cast_nonneg _) hDcap hstep.le
        _=_ := (Real.rpow_mul hz.le _ _).symm
    dsimp only [reserve]
    calc
      _≤Z^(Bseed*step)*Z^step*Z^(step/2) := by gcongr
      _=Z^((Bseed+3/2)*step) := by rw [←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
      _≤_ := Real.rpow_le_rpow_of_exponent_le hZ.le (reference_seed_budget B Bseed ε rho hB1 hBseed hε hrho)
  have hprofileC := control_pair_mono Sc control hSc s.W₁ s.W₂
  have hprofileR := control_pair_mono Sr control hSr s.W₁ s.W₂
  have hheightC : H^Jc*(1+|tp|)^Jc≤H^J*(1+|tp|)^J :=
    mul_le_mul (pow_le_pow_right₀ hH hJc) (pow_le_pow_right₀ htp hJc)
      (pow_nonneg (zero_le_one.trans htp) _) (pow_nonneg hH0 _)
  have hheightR : (height tp V s.t₁ s.t₂)^Jr≤H^J*(1+|tp|)^J := by
    calc
      _≤(H*(1+|tp|))^Jr := pow_le_pow_left₀ (by dsimp [height];positivity)
        (original_height_bound t₀ tp V s.t₁ s.t₂ hV) _
      _=H^Jr*(1+|tp|)^Jr := mul_pow _ _ _
      _≤_ := mul_le_mul (pow_le_pow_right₀ hH hJr) (pow_le_pow_right₀ htp hJr)
        (pow_nonneg (zero_le_one.trans htp) _) (pow_nonneg hH0 _)
  have hreference (X₁ X₂ : ℝ) (hx₁ : 0<X₁) (hx₂ : 0<X₂) (hXY : X₁*X₂=s.T)
      (hx₁B : X₁≤Z^B) (hx₂B : X₂≤Z^B)
      (henc₁ : b*X₁≤Cap*Z^Lcap) (henc₂ : b*X₂≤Cap*Z^Lcap)
      (hcenter : 5*R/6-7*d/3<P+S) (hshort : X₁≤Z^l ∨ X₂≤Z^l) :
      reserve*(∑F:selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        radialEnergy (fun z=>heightRectangle s ha
          (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
            (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
          tp X₁ X₂) (keep F.val) Φ K)≤radialControl Φ*Cr*cost := by
    have haR := hadZ.2 T hcardT a s hcanonical.1 hR hFhole hprod X₁ X₂
      hx₁B hx₂B henc₁ henc₂
    have he := hrZ.2 T s hMs α q hα hqP hqpool hqvolume hqvolumeCap hWcap Kslot hKslot
      hqν hqW η K X₁ X₂ S hK hx₁ hx₂ hS
    dsimp only at he
    rw [hXY] at he
    have he' := he hRcap hmixed hcenter hshort haR.1 haR.2.1 haR.2.2.1 haR.2.2.2.1
      haR.2.2.2.2.1 haR.2.2.2.2.2 hprodS tp t₀ V
      (fun i:T=>CenteredMomentNaturalFixedRaySource.relativeCharacter M Hray hHray η₀ (θ i.val))
      (fun i:T=>R₀ i.val) hV hcanonical.2.2.1 hHR Q keep hkeep heligible Φ hΦs
    have hp := mul_le_mul_of_nonneg_left he' hreserve
    apply hp.trans
    have haux : 0≤radialControl Φ*Cr*Kslot^(2*N)*
        (sourceControl Sr s.W₁*sourceControl Sr s.W₂)^2*(height tp V s.t₁ s.t₂)^Jr*
        ((η.modulus.absNorm:ℝ)*K) := by
      have hh : 0≤height tp V s.t₁ s.t₂ := by dsimp [height];positivity
      have hc := radial_control_nonneg Φ
      positivity
    calc
      _=(radialControl Φ*Cr*Kslot^(2*N)*(sourceControl Sr s.W₁*sourceControl Sr s.W₂)^2*
          (height tp V s.t₁ s.t₂)^Jr*((η.modulus.absNorm:ℝ)*K))*(reserve*Z^(step/2)) := by ring
      _≤(radialControl Φ*Cr*Kslot^(2*N)*(sourceControl Sr s.W₁*sourceControl Sr s.W₂)^2*
          (height tp V s.t₁ s.t₂)^Jr*((η.modulus.absNorm:ℝ)*K))*Z^ε :=
        mul_le_mul_of_nonneg_left hpay haux
      _≤radialControl Φ*Cr*cost := by
        dsimp only [cost,A]
        have hrc := radial_control_nonneg Φ
        calc
          _=(radialControl Φ*Cr*Kslot^(2*N)*((η.modulus.absNorm:ℝ)*K)*Z^ε)*
            ((sourceControl Sr s.W₁*sourceControl Sr s.W₂)^2*(height tp V s.t₁ s.t₂)^Jr) := by ring
          _≤(radialControl Φ*Cr*Kslot^(2*N)*((η.modulus.absNorm:ℝ)*K)*Z^ε)*
            ((sourceControl control s.W₁*sourceControl control s.W₂)^2*(H^J*(1+|tp|)^J)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul hprofileR hheightR (by dsimp [height];positivity) (sq_nonneg _)
          _=_ := by ring
  have hencOriginal₁ : b*s.X₁≤Cap*Z^Lcap :=
    mul_le_mul hCapb (hX₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
      (s.hL.trans_le s.hX₁).le (by linarith)
  have hencOriginal₂ : b*s.X₂≤Cap*Z^Lcap :=
    mul_le_mul hCapb (hX₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)))
      (s.hL.trans_le s.hX₂).le (by linarith)
  have hRcost : radialControl Φ*Cr*cost≤C*cost := by
    apply mul_le_mul_of_nonneg_right _ hcost
    have hc := radial_control_nonneg Φ
    dsimp only [C]
    nlinarith
  suffices hfinal : reserve*groupedMoment q s ha η tp keep Φ K≤C*cost by
    convert hfinal using 1 <;> dsimp only [reserve,step,cost,A,H] <;> ring
  by_cases htiny : s.X₁≤comparisonScale b ∨ s.X₂≤comparisonScale b
  · have he := grouped_uncentered_eq q s ha hd hG hY η tp keep hkeep Φ K
    have hzrect (F : selectedProducts q) (z : O) :
        heightRectangle s ha
          (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
            (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
          tp s.X₁ s.X₂=0 := height_rectangle_small s ha _ tp s.X₁ s.X₂
            (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) htiny
    simp only [hzrect,radialEnergy,norm_zero,zero_pow (by decide : 2≠0),zero_mul,
      ite_self,tsum_zero,mul_zero,Finset.sum_const_zero] at he
    rw [he,mul_zero]
    exact mul_nonneg hC.le hcost
  by_cases hshort : 5*R/6-7*d/3<P+S ∧ (s.X₁≤Z^l ∨ s.X₂≤Z^l)
  · rw [grouped_uncentered_eq q s ha hd hG hY η tp keep hkeep Φ K]
    exact (hreference s.X₁ s.X₂ (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) s.hpX
      hX₁B hX₂B hencOriginal₁ hencOriginal₂ hshort.1 hshort.2).trans hRcost
  let qref := qReference b Z R P S d
  have hq₁ : qref≤s.X₁ := by
    by_cases hun : P+S≤5*R/6-7*d/3
    · simpa only [qref,qReference,if_pos hun] using
        (le_of_lt (lt_of_not_ge (fun h=>htiny (Or.inl h))))
    · have hn : ¬s.X₁≤Z^l := fun h=>hshort ⟨lt_of_not_ge hun,Or.inl h⟩
      simpa only [qref,qReference,if_neg hun] using (le_of_lt (lt_of_not_ge hn))
  have hq₂ : qref≤s.X₂ := by
    by_cases hun : P+S≤5*R/6-7*d/3
    · simpa only [qref,qReference,if_pos hun] using
        (le_of_lt (lt_of_not_ge (fun h=>htiny (Or.inr h))))
    · have hn : ¬s.X₂≤Z^l := fun h=>hshort ⟨lt_of_not_ge hun,Or.inr h⟩
      simpa only [qref,qReference,if_neg hun] using (le_of_lt (lt_of_not_ge hn))
  let r := chosenReference s (zero_le_one.trans hb) Z R S d Lorig Lcap Cap hZ.le hLorig hLc
    hCapc hcanonical.1 hX₁ hX₂ hmix hq₁ hq₂
  have hrd := chosen_data s (zero_le_one.trans hb) Z R S d Lorig Lcap Cap hZ.le hLorig hLc
    hCapc hcanonical.1 hX₁ hX₂ hmix hq₁ hq₂
  obtain ⟨hrS,hrH,hrR,hrF,hrd,hrB,hrG,hrX₁,hrX₂,hrT,hrP,hrM,hrVol,
    hrY₁,hrY₂,hrL,cover,hlength,hfloor⟩ := hrd
  have hgeo := reference_length_geometry b Z R P S d hZ.le hmix
  have hcapr := hpZ.2 T a s hX₁ hX₂ qref hgeo.1 hq₁
  have hcr : Canonical M Hray hHray Wslot Cap Lcap Z η₀
      (fun i:T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) r :=
    chosen_canonical M Hray hHray Wslot Cap Lcap Z Lorig η₀
      (fun i:T=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val)
      t₀ (fun i=>R₀ i.val) s hcanonical (zero_le_one.trans hb) R S d hZ.le hLorig hLc
      hCapc hX₁ hX₂ hmix hq₁ hq₂
  have hcentered : reserve*groupedMoment q r ha η tp keep Φ K≤Cc*cost := by
    by_cases hsharp : 1≤sharpSupport r
    · have he := hcZ.2 T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ r hcr hd hMs
        hR hHholes hholes hHR hFhole hcapr.1 hcapr.2.1 hcapr.2.2.1
        hcapr.2.2.2.1 hcapr.2.2.2.2 hprod cover η hη K hK hKcap hKinv hsharp
        χ₀ msecond hm hml hm2 1 (one_dvd _) α q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
        hR0 hmixed hnative hlength Dseed hDseed hDcap
      have hg := mul_le_mul_of_nonneg_left
        (grouped_moment_le_chosen q hqP r ha η tp keep Φ K hK hΦs hΦ) hreserve
      apply (hg.trans he).trans
      change Cc*Kslot^(2*N)*(sourceControl Sc s.W₁*sourceControl Sc s.W₂)^2*
        H^Jc*(1+|tp|)^Jc*((η.modulus.absNorm:ℝ)*K)*Z^ε≤Cc*cost
      calc
        _=(Cc*Kslot^(2*N)*((η.modulus.absNorm:ℝ)*K)*Z^ε)*
          ((sourceControl Sc s.W₁*sourceControl Sc s.W₂)^2*(H^Jc*(1+|tp|)^Jc)) := by ring
        _≤(Cc*Kslot^(2*N)*((η.modulus.absNorm:ℝ)*K)*Z^ε)*
          ((sourceControl control s.W₁*sourceControl control s.W₂)^2*(H^J*(1+|tp|)^J)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul hprofileC hheightC (by positivity) (sq_nonneg _)
        _=_ := by dsimp only [cost,A];ring
    · have he : groupedMoment q r ha η tp keep Φ K=0 := by
        simp only [groupedMoment,selected_energy_zero_of_sharp_small r ha (lt_of_not_ge hsharp),
          mul_zero,Finset.sum_const_zero,zero_div]
      rw [he,mul_zero]
      exact mul_nonneg hCc.le hcost
  let refEnergy (F : selectedProducts q) : ℝ :=
    radialEnergy (fun z=>heightRectangle s ha
      (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
        (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
      tp r.Y₁ r.Y₂) (keep F.val) Φ K
  let refAverage := ∑F:selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*refEnergy F
  have hreferenceChosen : reserve*refAverage≤radialControl Φ*Cr*cost := by
    by_cases hun : P+S≤5*R/6-7*d/3
    · have hrzero (F : selectedProducts q) : refEnergy F=0 := by
        have he (z : O) : heightRectangle s ha
            (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
              (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
            tp r.Y₁ r.Y₂=0 :=
          chosen_uncentered_zero s (zero_le_one.trans hb) Z R S d Lorig Lcap Cap hZ.le
            hLorig hLc hCapc hcanonical.1 hX₁ hX₂ hmix hq₁ hq₂ ha _ tp hun
        simp only [refEnergy,he,radialEnergy,norm_zero,zero_pow (by decide : 2≠0),
          zero_mul,ite_self,tsum_zero]
      simp only [refAverage,hrzero,mul_zero,Finset.sum_const_zero]
      have hrc := radial_control_nonneg Φ
      positivity
    · have hcaps := enclosure_caps s (zero_le_one.trans hb) Z Lorig Lcap Cap qref hZ.le hLorig
        hLc hCapc hX₁ hX₂ hgeo.1 hq₁
      have hshortref : r.Y₁≤Z^l ∨ r.Y₂≤Z^l := Or.inl (by
        change qReference b Z R P S d≤Z^l
        simp only [qReference,if_neg hun,l,le_refl])
      exact hreference r.Y₁ r.Y₂ (r.hL.trans_le r.hY₁) (r.hL.trans_le r.hY₂) r.hpY
        hcapr.2.2.2.1 hcapr.2.2.2.2 hcaps.2.2.1 hcaps.2.2.2
        (lt_of_not_ge hun) hshortref
  have hpoint (F : selectedProducts q) :
      selectedEnergy s ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K/sourceVolume s≤
        2*(selectedEnergy r ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K/sourceVolume r+
          refEnergy F) := by
    let f : O→ℂ := fun z=>normalization (s.X₁*s.X₂) s.P*
      selectedPolynomial s ha 1 F.val η fixedBadMask 1 tp z
    let g : O→ℂ := fun z=>normalization (r.X₁*r.X₂) r.P*
      selectedPolynomial r ha 1 F.val η fixedBadMask 1 tp z
    let h : O→ℂ := fun z=>heightRectangle s ha
      (selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
        (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z)
      tp r.Y₁ r.Y₂
    have he (z : O) (hzkeep : keep F.val z) : f z=g z+h z := by
      have hn := hkeep F.val F.property z hzkeep
      let χ := Classical.choice (selected_character_exists η fixedBadMask F.val z
        fixedBadMask_ne_zero (selected_products_supported q F.val F.property) hn
        (dvd_mul_right _ _) (dvd_mul_left _ _))
      have hc : selectedCharacterAt η fixedBadMask F.val fixedBadMask_ne_zero
          (selected_products_supported q F.val F.property) (dvd_mul_right _ _) (dvd_mul_left _ _) z=
          χ.character := by rw [selectedCharacterAt,dif_pos hn]
      dsimp only [f,g,h]
      rw [hc]
      exact chosen_selected_split s (zero_le_one.trans hb) Z R S d Lorig Lcap Cap hZ.le hLorig hLc
        hCapc hcanonical.1 hX₁ hX₂ hmix hq₁ hq₂ ha hd hG hY η fixedBadMask F.val z
        (dvd_mul_right _ _) (dvd_mul_left _ _) χ tp
    have he := radial_split f g h (keep F.val) he Φ K hK hΦs hΦ
    dsimp only [f,g,h] at he
    rw [normalized_energy s ha F.val η tp (keep F.val) Φ K,
      normalized_energy r ha F.val η tp (keep F.val) Φ K] at he
    exact he
  have hsplit : groupedMoment q s ha η tp keep Φ K≤2*(groupedMoment q r ha η tp keep Φ K+refAverage) := by
    calc
      _=∑F:selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
          (selectedEnergy s ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K/sourceVolume s) := by
        simp only [groupedMoment,Finset.sum_div,mul_div_assoc]
      _≤∑F:selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
          (2*(selectedEnergy r ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K/sourceVolume r+refEnergy F)) := by
        apply Finset.sum_le_sum
        intro F hF
        exact mul_le_mul_of_nonneg_left (hpoint F)
          (div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hqP).le)
      _=_ := by
        simp only [groupedMoment,refAverage,Finset.sum_div]
        rw [mul_add]
        simp only [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro F hF
        ring
  calc
    _≤reserve*(2*(groupedMoment q r ha η tp keep Φ K+refAverage)) :=
      mul_le_mul_of_nonneg_left hsplit hreserve
    _=2*(reserve*groupedMoment q r ha η tp keep Φ K+reserve*refAverage) := by ring
    _≤2*(Cc*cost+radialControl Φ*Cr*cost) :=
      mul_le_mul_of_nonneg_left (add_le_add hcentered hreferenceChosen) (by norm_num)
    _=C*cost := by dsimp only [C];ring

end
end Candidate.FourthPower.MixedFirstSourceMoment
