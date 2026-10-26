/- Copyright (c) 2026 Sil. Apache-2.0.
Fourier lifting of the SAME selected-product/physical-row vector.
The public endpoint below calls the actual SourceMoment theorem. The
conditional integral transport is private, not a new moment assumption.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstSeededMoment
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstSourceMoment
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstCenteredSourceMoment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstSourceWindow
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CompletedGauss (primaryGenerator)
open CanonicalRowCompletion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentHeckeExpansion CenteredMomentOriginalRadialComparison
open CenteredMomentEnergyCapacityRemoval CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSecondHeightFamily
open CenteredMomentUncenteredTerminal CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedInnerExceptionalBlock MixedFirstPhysicalApplication MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceMoment MixedFirstProfileEnvelope
open MixedFirstCenteredSourceMoment MixedFirstSeededMoment
open QRH.Record1252270103KernelMass
open MixedSupplierFourthRow MixedSupplierPositive MixedCanonicalSource ReferencePrimeEnclosure
open MixedFirstUniformLossBudget MixedFirstChosenEnergy MixedFirstReferenceChoice
open MixedFirstActualNonexceptional
open CenteredExceptionalProfile MixedFirstGeometricCaps
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- Only a literal common Fourier window is added to the original
selected coefficients. The selected F, mask, height and seed remain. -/
def windowedPolynomial (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (m A : O) (tp : ℝ) (Vwin : ℝ→ℂ) (X θ : ℝ) (z : O) : ℂ :=
  ∑I∈sourceColumns s,selectedCoefficient s ha seed F I*rowWeight η m A z tp I*
    columnPhase Vwin (Real.log ((I.absNorm:ℝ)/X)) θ

private theorem weight_height (η : Character) (m A z : O) (t : ℝ) (I : Id) :
    rowWeight η m A z t I=heightCoeff η t I*idealRowHom (m^6*(A*z)) I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(I.absNorm:ℂ)^(Complex.I*t)=_
  unfold heightCoeff
  ring

private theorem selected_integrable (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (m A : O) (tp : ℝ)
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (X θ : ℝ) (hX : 0<X) (z : O) :
    Integrable (fun w : ℝ=>columnDensity Vwin hVc hVs w*logPhase (θ-w) (Real.log X)*
      selectedPolynomial s ha seed F η m A (tp+2*Real.pi*(w-θ)) z) := by
  have hi (I : Id) (_hI : I∈sourceColumns s) :
      Integrable (fun w : ℝ=>selectedCoefficient s ha seed F I*
        (columnDensity Vwin hVc hVs w*logPhase (θ-w) (Real.log X)*
          rowWeight η m A z (tp+2*Real.pi*(w-θ)) I)) := by
    by_cases hI : I=0
    · subst I
      simp only [map_zero,mul_zero]
      exact integrable_zero ℝ ℂ volume
    · have hh := ((height_column_integrable Vwin hVc hVs η I hI tp θ X hX).const_mul
        (selectedCoefficient s ha seed F I)).mul_const (idealRowHom (m^6*(A*z)) I)
      convert hh using 1
      funext w
      rw [weight_height]
      ring
  convert integrable_finsetSum (sourceColumns s) hi using 1
  funext w
  simp only [selectedPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- Exact integral before any estimate. Its density and log window are
common to every selected product; all F-dependence remains in the row. -/
theorem selected_window_integral (s : Source ι a b) (ha : 0<a) (seed F : Id)
    (η : Character) (m A : O) (tp : ℝ)
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (X θ : ℝ) (hX : 0<X) (z : O) :
    windowedPolynomial s ha seed F η m A tp Vwin X θ z=
      ∫w : ℝ,columnDensity Vwin hVc hVs w*logPhase (θ-w) (Real.log X)*
        selectedPolynomial s ha seed F η m A (tp+2*Real.pi*(w-θ)) z := by
  have hpoint (I : Id) :
      selectedCoefficient s ha seed F I*rowWeight η m A z tp I*
          columnPhase Vwin (Real.log ((I.absNorm:ℝ)/X)) θ=
        ∫w : ℝ,selectedCoefficient s ha seed F I*
          (columnDensity Vwin hVc hVs w*logPhase (θ-w) (Real.log X)*
            rowWeight η m A z (tp+2*Real.pi*(w-θ)) I) := by
    by_cases hI : I=0
    · subst I
      simp only [map_zero,mul_zero,zero_mul,integral_zero]
    · simp_rw [weight_height]
      rw [show selectedCoefficient s ha seed F I*
        (heightCoeff η tp I*idealRowHom (m^6*(A*z)) I)*
        columnPhase Vwin (Real.log ((I.absNorm:ℝ)/X)) θ=
          (selectedCoefficient s ha seed F I*idealRowHom (m^6*(A*z)) I)*
            (heightCoeff η tp I*columnPhase Vwin (Real.log ((I.absNorm:ℝ)/X)) θ) by ring]
      rw [height_column_integral Vwin hVc hVs η I hI tp θ X hX,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      ring
  have hi (I : Id) (_hI : I∈sourceColumns s) :
      Integrable (fun w : ℝ=>selectedCoefficient s ha seed F I*
        (columnDensity Vwin hVc hVs w*logPhase (θ-w) (Real.log X)*
          rowWeight η m A z (tp+2*Real.pi*(w-θ)) I)) := by
    by_cases hI : I=0
    · subst I
      simp only [map_zero,mul_zero]
      exact integrable_zero ℝ ℂ volume
    · have hh := ((height_column_integrable Vwin hVc hVs η I hI tp θ X hX).const_mul
        (selectedCoefficient s ha seed F I)).mul_const (idealRowHom (m^6*(A*z)) I)
      convert hh using 1
      funext w
      rw [weight_height]
      ring
  unfold windowedPolynomial
  simp_rw [hpoint]
  rw [←integral_finsetSum _ hi]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [selectedPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

private def radialWeight (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (z : O) : ℝ :=
  if keep z then (Φ (‖eisEmbedding z‖^2/K)).re else 0

/-- Finite physical rows, suitable for the existing whole-kernel theorem.
There is one selected-scale denominator and one source-volume denominator. -/
def groupedWindowRows {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (Vwin : ℝ→ℂ) (X θ : ℝ) (rows : Finset O) : ℝ :=
  (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,(if keep F.val z then (Φ (‖eisEmbedding z‖^2/K)).re else 0)*
      ‖windowedPolynomial s ha 1 F.val η fixedBadMask 1 tp Vwin X θ z‖^2)/sourceVolume s

/-- The literal full artificial seed in the same selected/window vector.
The scale and source-volume denominators occur only once. -/
def seededGroupedWindowRows {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (D : Id) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (Vwin : ℝ→ℂ) (X θ : ℝ) (rows : Finset O) : ℝ :=
  (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,(if keep F.val z then (Φ (‖eisEmbedding z‖^2/K)).re else 0)*
      ‖windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z‖^2)/sourceVolume s

theorem seeded_grouped_window_one {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (η : Character) (tp : ℝ)
    (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (Vwin : ℝ→ℂ) (X θ : ℝ) (rows : Finset O) :
    seededGroupedWindowRows q s ha 1 η tp keep Φ K Vwin X θ rows=
      groupedWindowRows q s ha η tp keep Φ K Vwin X θ rows := rfl

private theorem finite_rows_le (s : Source ι a b) (ha : 0<a) (D F : Id)
    (η : Character) (tp : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hK : 0<K) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2)
    (hΦ : ∀x,0≤(Φ x).re) (rows : Finset O) :
    (∑z∈rows,radialWeight keep Φ K z*
      ‖selectedPolynomial s ha D F η fixedBadMask 1 tp z‖^2)≤
      selectedEnergy s ha D F η fixedBadMask 1 tp keep Φ K := by
  have hs := compact_radial_summable
    (selectedPolynomial s ha D F η fixedBadMask 1 tp) keep Φ K 2 hK hΦs
  have hh := sum_le_hasSum rows (fun z _=>show 0≤
      (if keep z then ‖selectedPolynomial s ha D F η fixedBadMask 1 tp z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) from by
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (hΦ _)
      · exact le_rfl) hs.hasSum
  simpa only [selectedEnergy,radialEnergy,radialWeight,ite_mul,mul_ite,zero_mul,mul_zero,mul_comm] using hh


private theorem product_sum {κ γ : Type*} [Fintype κ] [Fintype γ]
    (c : ℝ) (w : κ→ℝ) (r : κ→γ→ℝ) (f : κ→γ→ℂ) :
    (∑p : κ×γ,c*w p.1*r p.1 p.2*‖f p.1 p.2‖^2)=
      c*(∑F,w F*(∑z,r F z*‖f F z‖^2)) := by
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

set_option maxHeartbeats 800000 in
/-- Pure integral transport. This is PRIVATE: the actual public theorem
below supplies hmoment by calling the actual seeded source theorem, rather than
making an energy estimate an additional input to the source theorem. -/
private theorem grouped_window_from_height {α : Type v} [Fintype α]
    (q : Data α) (hqP : ∀i,0<q.P i) (s : Source ι a b) (ha : 0<a) (D : Id)
    (η : Character) (keep : Id→O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hK : 0<K) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2)
    (hΦ : ∀x,0≤(Φ x).re) (save E : ℝ) (hsave : 0≤save) (hE : 0≤E) (J : ℕ)
    (hmoment : ∀v : ℝ,save*seededGroupedMoment q s ha D η v keep Φ K≤E*(1+‖v‖)^(2*J))
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (tp θ X : ℝ) (hX : 0<X) (rows : Finset O) :
    save*seededGroupedWindowRows q s ha D η tp keep Φ K Vwin X θ rows≤
      (E*heightCost tp θ^(2*J))*(∫w : ℝ,(1+‖w‖)^J*‖columnDensity Vwin hVc hVs w‖)^2 := by
  let selectedMass : selectedProducts q→ℝ := fun F=>groupedWeight q F.val/MixedSelectedVolume.scale q
  let r : selectedProducts q→O→ℝ := fun F z=>radialWeight (keep F.val) Φ K z
  let μ : selectedProducts q×rows→ℝ := fun p=>save/sourceVolume s*selectedMass p.1*r p.1 p.2
  have hselectedMass (F : selectedProducts q) : 0≤selectedMass F :=
    div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hqP).le
  have hr (F : selectedProducts q) (z : O) : 0≤r F z := by
    dsimp only [r,radialWeight]
    split_ifs
    · exact hΦ _
    · exact le_rfl
  have hμ (p : selectedProducts q×rows) : 0≤μ p :=
    mul_nonneg (mul_nonneg (div_nonneg hsave (sourceVolume_pos s).le) (hselectedMass p.1)) (hr p.1 p.2)
  have hnorm (p : selectedProducts q×rows) (z : ℂ) :
      ‖(Real.sqrt (μ p):ℂ)*z‖^2=μ p*‖z‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,Real.sq_sqrt (hμ p)]
  let φ := fun (p : selectedProducts q×rows) (w : ℝ)=>
    (Real.sqrt (μ p):ℂ)*(logPhase (θ-w) (Real.log X)*
      selectedPolynomial s ha D p.1.val η fixedBadMask 1 (tp+2*Real.pi*(w-θ)) p.2.val)
  have hi (p : selectedProducts q×rows) :
      Integrable (fun w=>columnDensity Vwin hVc hVs w*φ p w) := by
    have hh := (selected_integrable s ha D p.1.val η fixedBadMask 1 tp
      Vwin hVc hVs X θ hX p.2.val).const_mul (Real.sqrt (μ p):ℂ)
    convert hh using 1
    funext w
    dsimp only [φ]
    ring
  have hfinite (v : ℝ) :
      (∑p : selectedProducts q×rows,μ p*
        ‖selectedPolynomial s ha D p.1.val η fixedBadMask 1 v p.2.val‖^2)≤
        save*seededGroupedMoment q s ha D η v keep Φ K := by
    change (∑p : selectedProducts q×rows,save/sourceVolume s*selectedMass p.1*r p.1 p.2*
      ‖selectedPolynomial s ha D p.1.val η fixedBadMask 1 v p.2.val‖^2)≤_
    rw [product_sum (save/sourceVolume s) selectedMass
      (fun F (z : rows)=>r F z.val)
      (fun F (z : rows)=>selectedPolynomial s ha D F.val η fixedBadMask 1 v z.val)]
    have hh : (∑F : selectedProducts q,selectedMass F*
        (∑z : rows,r F z*‖selectedPolynomial s ha D F.val η fixedBadMask 1 v z.val‖^2))≤
        ∑F : selectedProducts q,selectedMass F*selectedEnergy s ha D F.val η fixedBadMask 1 v (keep F.val) Φ K := by
      apply Finset.sum_le_sum
      intro F hF
      apply mul_le_mul_of_nonneg_left _ (hselectedMass F)
      rw [Finset.sum_coe_sort rows (fun z=>r F z*
        ‖selectedPolynomial s ha D F.val η fixedBadMask 1 v z‖^2)]
      exact finite_rows_le s ha D F.val η v (keep F.val) Φ K hK hΦs hΦ rows
    exact (mul_le_mul_of_nonneg_left hh (div_nonneg hsave (sourceVolume_pos s).le)).trans_eq (by
      dsimp only [seededGroupedMoment,selectedMass]
      ring)
  have hφnorm (p : selectedProducts q×rows) (w : ℝ) :
      ‖φ p w‖^2=μ p*
        ‖selectedPolynomial s ha D p.1.val η fixedBadMask 1
          (tp+2*Real.pi*(w-θ)) p.2.val‖^2 := by
    dsimp only [φ]
    rw [hnorm,norm_mul,logPhase_norm,one_mul]
  have hb (w : ℝ) : (∑p : selectedProducts q×rows,‖φ p w‖^2)≤
      (E*heightCost tp θ^(2*J))*((1+‖w‖)^J)^2 := by
    simp only [hφnorm]
    calc
      _≤E*(1+‖tp+2*Real.pi*(w-θ)‖)^(2*J) :=
        (hfinite _).trans (hmoment _)
      _≤E*(heightCost tp θ*(1+‖w‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (norm_height_shift tp θ w) _) hE
      _=_ := by
        simp only [mul_pow,←pow_mul,Nat.mul_comm J 2]
        ring
  have hh := finite_weighted_integral_energy (columnDensity Vwin hVc hVs) φ
    (fun w=>(1+‖w‖)^J) (by intro w;positivity)
    (E*heightCost tp θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos tp θ).le _))
    (columnDensity_moments Vwin hVc hVs J) hi hb
  have hid (p : selectedProducts q×rows) :
      (∫w : ℝ,columnDensity Vwin hVc hVs w*φ p w)=
        (Real.sqrt (μ p):ℂ)*windowedPolynomial s ha D p.1.val η fixedBadMask 1 tp Vwin X θ p.2.val := by
    rw [selected_window_integral s ha D p.1.val η fixedBadMask 1 tp Vwin hVc hVs X θ hX p.2.val,
      ←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    dsimp only [φ]
    ring
  simp only [hid,hnorm] at hh
  have hout : (∑p : selectedProducts q×rows,μ p*
      ‖windowedPolynomial s ha D p.1.val η fixedBadMask 1 tp Vwin X θ p.2.val‖^2)=
      save*seededGroupedWindowRows q s ha D η tp keep Φ K Vwin X θ rows := by
    change (∑p : selectedProducts q×rows,save/sourceVolume s*selectedMass p.1*r p.1 p.2*
      ‖windowedPolynomial s ha D p.1.val η fixedBadMask 1 tp Vwin X θ p.2.val‖^2)=_
    rw [product_sum (save/sourceVolume s) selectedMass
      (fun F (z : rows)=>r F z.val)
      (fun F (z : rows)=>windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z.val)]
    have hsums (F : selectedProducts q) :
        (∑z : rows,r F z.val*
          ‖windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z.val‖^2)=
        ∑z∈rows,r F z*
          ‖windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z‖^2 :=
      Finset.sum_coe_sort rows (fun z=>r F z*
        ‖windowedPolynomial s ha D F.val η fixedBadMask 1 tp Vwin X θ z‖^2)
    simp_rw [hsums]
    simp only [seededGroupedWindowRows,selectedMass,r,radialWeight]
    ring
  rw [hout] at hh
  exact hh


variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Actual source application. There is no energy, row count or Fourier
decay hypothesis. The bound at EVERY independent physical height is
obtained from uniform_centered_source_moment and inserted in the private finite
integral transport on the single index (F,z).

The density Vwin is fixed before J, the constants, sources and F. The
finite moment on the RHS exists by columnDensity_moments for this J;
it adds no Z loss. The original seed AND Z reserve stay on the left.
The keep predicate can depend on F, but is unchanged during integration.
-/
theorem uniform_unit_selected_column_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
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
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
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
    ∀X θwin : ℝ,0<X→∀rows : Finset O,
    ((Dseed.absNorm:ℝ)^step*Z^step)*
      groupedWindowRows q s ha η tp keep Φ K Vwin X θwin rows≤
      C*Kslot^(2*N)*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*heightCost tp θwin^(2*J)*
        (∫w : ℝ,(1+‖w‖)^J*‖columnDensity Vwin hVc hVs w‖)^2*
        ((η.modulus.absNorm:ℝ)*K)*Z^ε := by
  dsimp only
  obtain ⟨J,control,hsource⟩ := uniform_centered_source_moment (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hsource⟩ := hsource η₀ hη₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hsource] with Z hsourceZ
  have hZ : 1<Z := hsourceZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  refine ⟨hsourceZ.1,?_⟩
  intro T θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hd hG hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap X θwin hX rows
  let save := (Dseed.absNorm:ℝ)^(budgetStep B Bseed ε rho)*Z^(budgetStep B Bseed ε rho)
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := height t₀ V s.t₁ s.t₂
  let E := C*Kslot^(2*N)*A^2*H^J*((η.modulus.absNorm:ℝ)*K)*Z^ε
  have hH : 0≤H := by dsimp only [H,height];positivity
  have hE : 0≤E := by dsimp only [E];positivity
  have hsave : 0≤save := by dsimp only [save];positivity
  have hall (v : ℝ) : save*groupedMoment q s ha η v keep Φ K≤E*(1+‖v‖)^(2*J) := by
    have hh := hsourceZ.2 T θ w σ freq t₀ v V R₀ hw hwL hσ hσhi hV hfreq hR₀
      s hcanonical hd hG hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂
      η hη K hK hKcap hKinv χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW
      hWcap hWinv hqvolume hR0 hmixed hnative keep hkeep heligible Dseed hDseed hDcap
    have hh' : save*groupedMoment q s ha η v keep Φ K≤E*(1+‖v‖)^J := by
      convert hh using 1 <;> dsimp only [save,E,A,H] <;>
        simp only [Real.norm_eq_abs] <;> ring
    exact hh'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) (by omega : J≤2*J)) hE)
  have he := grouped_window_from_height q hqP s ha 1 η keep Φ K hK hΦs hΦ
    save E hsave hE J hall Vwin hVc hVs tp θwin X hX rows
  apply he.trans_eq
  dsimp only [E,A,H]
  ring


/-- The actual radial disk is too small to contain a nonzero Eisenstein
integer. This uses the proved presentation factor, not a new row cap. -/
theorem radial_profile_zero_of_negative_width (η : Character) (K Z : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hR : inputWidth η K Z<0)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2)
    (z : O) (hz : z≠0) : Φ (‖eisEmbedding z‖^2/K)=0 := by
  have hsmall : 2*K<1 :=
    (MixedFirstReferenceActualCaps.actual_row_disk_cap η K Z hK hZ).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hZ hR)
  have hnorm := EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq z hz
  by_contra hvalue
  have hsupport : ‖eisEmbedding z‖^2/K≤2 := hΦs hvalue
  have hupper := (div_le_iff₀ hK).mp hsupport
  linarith

/-- Arbitrary actual row coefficients are allowed; the radial weights
themselves vanish. Positivity of Phi and any character gate are unnecessary. -/
theorem radial_energy_zero_of_negative_width (η : Character) (K Z : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hR : inputWidth η K Z<0)
    (f : O→ℂ) (keep : O→Prop) (hkeep : ∀z,keep z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) :
    radialEnergy f keep Φ K=0 := by
  unfold radialEnergy
  calc
    _ = ∑' _z : O,(0:ℝ) := by
      apply tsum_congr
      intro z
      by_cases hz : keep z
      · simp only [if_pos hz,
          radial_profile_zero_of_negative_width η K Z hK hZ hR Φ hΦs z (hkeep z hz),
          Complex.zero_re,mul_zero]
      · simp only [if_neg hz]
    _ = 0 := tsum_zero

/-- The original selected-product average, including its exact source
volume denominator and F-dependent keep, is zero when inputWidth<0. -/
theorem grouped_moment_zero_of_negative_width {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (η : Character) (tp K Z : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hR : inputWidth η K Z<0)
    (keep : Id→O→Prop) (hkeep : ∀F∈selectedProducts q,∀z,keep F z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2) :
    groupedMoment q s ha η tp keep Φ K=0 := by
  have hzero (F : selectedProducts q) :
      selectedEnergy s ha 1 F.val η fixedBadMask 1 tp (keep F.val) Φ K=0 :=
    radial_energy_zero_of_negative_width η K Z hK hZ hR
      (selectedPolynomial s ha 1 F.val η fixedBadMask 1 tp)
      (keep F.val) (hkeep F.val F.property) Φ hΦs
  unfold groupedMoment
  simp only [hzero,mul_zero,Finset.sum_const_zero,zero_div]



/-- The actual finite Fourier-window vector vanishes in negative width.
No bound or regularity assumption on its coefficients/window is needed. -/
theorem grouped_window_rows_zero_of_negative_width {α : Type v} [Fintype α] (q : Data α)
    (s : Source ι a b) (ha : 0<a) (η : Character) (tp K Z : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hR : inputWidth η K Z<0)
    (keep : Id→O→Prop) (hkeep : ∀F∈selectedProducts q,∀z,keep F z→z≠0)
    (Φ : 𝓢(ℝ,ℂ)) (hΦs : Function.support (Φ : ℝ→ℂ)⊆Iic 2)
    (Vwin : ℝ→ℂ) (X θ : ℝ) (rows : Finset O) :
    groupedWindowRows q s ha η tp keep Φ K Vwin X θ rows=0 := by
  have hzero (F : selectedProducts q) :
      (∑z∈rows,(if keep F.val z then (Φ (‖eisEmbedding z‖^2/K)).re else 0)*
        ‖windowedPolynomial s ha 1 F.val η fixedBadMask 1 tp Vwin X θ z‖^2)=0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hk : keep F.val z
    · simp only [if_pos hk,
        radial_profile_zero_of_negative_width η K Z hK hZ hR Φ hΦs z
          (hkeep F.val F.property z hk),Complex.zero_re,zero_mul]
    · simp only [if_neg hk,zero_mul]
  unfold groupedWindowRows
  simp only [hzero,mul_zero,Finset.sum_const_zero,zero_div]

/-- The full centered, original-prefix and artificial-seed source theorem
with its actual common Fourier window. No energy estimate is an input:
the private transport receives uniform_seeded_source_moment at every
physical height, while the canonical height t0 and F-dependent keep stay
fixed. The reciprocal original prefix/seed and all frozen profile factors
occur once, exactly as in the actual source theorem. -/
theorem uniform_seeded_selected_column_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
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
    let step:=budgetStep B Bseed ε rho
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀
      θ w σ freq t₀ R₀ s→s.B=(fun _=>1)→(∀i,s.M i≤Kslot)→
      (s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀K : ℝ,0<K→K≤Z^B→K⁻¹≤Z^B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀(α : Type v) [Fintype α],∀q : Data α,
      Fintype.card α≤N→(∀i,0<q.P i)→(∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i)→
      (∀i,∀I∈q.pool i,‖q.ν i I‖≤1)→(∀i x,‖q.Wslot i x‖≤Kslot)→
      MixedSelectedVolume.scale q≤Z^B→(MixedSelectedVolume.scale q)⁻¹≤Z^B→
      1≤MixedSelectedVolume.volume q→
    let R:=inputWidth η K Z
    let P:=Real.logb Z (s.T/pairNorm s.d)
    let S:=∑i,w i
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    0≤R→P+2*S+4*d≤R-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    ∀X θwin : ℝ,0<X→∀rows : Finset O,
    Z^step*seededGroupedWindowRows q s ha D η tp keep Φ K Vwin X θwin rows≤
      C*Kslot^(2*N)*(∏i,s.M i)^2*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^J*heightCost tp θwin^(2*J)*
        (∫w : ℝ,(1+‖w‖)^J*‖columnDensity Vwin hVc hVs w‖)^2*
        ((η.modulus.absNorm:ℝ)*K)*Z^ε/(pairNorm s.d*(D.absNorm:ℝ)) := by
  dsimp only
  obtain ⟨J,control,hsource⟩ := uniform_seeded_source_moment (ι:=ι) M Hray hHray
    Φ N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho
    hΦs hΦ hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap hslots hCap hCapc
    hBR0 hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨J,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hsource⟩ := hsource η₀ hη₀
  refine ⟨C,hC,?_⟩
  filter_upwards [hsource] with Z hsourceZ
  have hZ : 1<Z := hsourceZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  refine ⟨hsourceZ.1,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hBunit hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ η hη K hK hKcap hKinv
    χ₀ msecond hm hml hm2 α instα q hα hqP hqpool hqν hqW hWcap hWinv hqvolume
    hR0 hmixed hnative keep hkeep heligible D hD hDcap X θwin hX rows
  let save := Z^(budgetStep B Bseed ε rho)
  let A := sourceControl control s.W₁*sourceControl control s.W₂
  let H := height t₀ V s.t₁ s.t₂
  let E := C*Kslot^(2*N)*(∏i,s.M i)^2*A^2*H^J*((η.modulus.absNorm:ℝ)*K)*Z^ε/
    (pairNorm s.d*(D.absNorm:ℝ))
  have hH : 0≤H := by dsimp only [H,height];positivity
  have hp : 0<pairNorm s.d := pairNorm_pos s.hd.1 s.hd.2
  have hDnorm : 0<(D.absNorm:ℝ) :=
    zero_lt_one.trans_le (QRH.Record1252270103KernelMass.ideal_norm_one_le hD.ne_zero)
  have hE : 0≤E := by dsimp only [E];positivity
  have hsave : 0≤save := Real.rpow_nonneg hz.le _
  have hall (v : ℝ) : save*seededGroupedMoment q s ha D η v keep Φ K≤
      E*(1+‖v‖)^(2*J) := by
    have hh := hsourceZ.2 θ w σ freq t₀ v V R₀ hw hwL hσ hσhi hV hfreq hR₀
      s hcanonical hBunit hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂
      η hη K hK hKcap hKinv χ₀ msecond hm hml hm2 α q hα hqP hqpool hqν hqW
      hWcap hWinv hqvolume hR0 hmixed hnative keep hkeep heligible D hD hDcap
    have hh' : save*seededGroupedMoment q s ha D η v keep Φ K≤E*(1+‖v‖)^J := by
      convert hh using 1 <;> dsimp only [save,E,A,H] <;>
        simp only [Real.norm_eq_abs] <;> ring
    exact hh'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) (by omega : J≤2*J)) hE)
  have he := grouped_window_from_height q hqP s ha D η keep Φ K hK hΦs hΦ
    save E hsave hE J hall Vwin hVc hVs tp θwin X hX rows
  apply he.trans_eq
  dsimp only [E,A,H]
  ring

end
end Candidate.FourthPower.MixedFirstSourceWindow
