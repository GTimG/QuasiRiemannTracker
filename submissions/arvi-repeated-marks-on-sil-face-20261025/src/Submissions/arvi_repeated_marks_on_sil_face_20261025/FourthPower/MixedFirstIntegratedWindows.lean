/- Copyright (c) 2026 Sil. Apache-2.0.
The actual all-height four-part suppliers integrated through the first
column windows. The fourth-power average and distinct child scales stay
literal. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstAveragedWindow
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstFullBudget
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstAvoidance
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.IncumbentInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstIntegratedWindows
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource MixedFirstActualNonexceptional
open CenteredMomentCanonicalFirst CenteredMomentFirstMixedAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedRightTransport CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstWindowBudgets
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentSmoothedWindowEnergy
open CenteredMomentHeckeWindowEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondWindowSource
open CenteredMomentGaussEnergy CenteredMomentNaturalFixedRaySource CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open CenteredMomentCauchy CenteredMomentSmooth FourierBridge
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap MixedOriginalTail
open MixedOriginalSecondZero MixedFirstLiveSource MixedFirstFourParts
open MixedFirstNonexceptionalAllocation MixedFirstReferencePair MixedFirstInactiveConductor
open MixedFirstExceptionalNormalization MixedFirstExceptionalApplication MixedInnerExceptionalBlock
open MixedFirstFullBudget MixedFirstAveragedWindow MixedHeightEnvelope
open MixedFirstAvoidance
open ReferencePrimeEnclosure MixedCompletedRows QuadraticInitialBound
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def degree (U : Controls) : ℕ := U.nonexceptionalDegree+U.exceptionalDegree

/-- The two fourth-power transfers retain their distinct actual radii.
The averaging factor 1/W is already in each outputEnergy. -/
def pushCost (Cpush mass KL KR W ε : ℝ) : ℝ :=
  Real.sqrt (mass*Cpush*(16*KL*W^4)^ε)*
    Real.sqrt (mass*Cpush*(16*KR*W^4)^ε)

private def componentDegree (U : Controls) : Fin 4→ℕ :=
  ![0,U.nonexceptionalDegree,U.exceptionalDegree,0]

private theorem height_ratio_le (v : ℝ) :
    heightEnvelope v/heightEnvelope 0≤1+‖v‖ := by
  apply (div_le_iff₀ (heightEnvelope_pos 0)).mpr
  have hlin : 1+‖v‖+2*Real.pi≤(1+2*Real.pi)*(1+‖v‖) := by
    nlinarith [norm_nonneg v,Real.pi_pos]
  have hm := mul_le_mul_of_nonneg_right hlin (by positivity : 0≤1+2*Real.pi)
  convert hm using 1 <;> simp only [heightEnvelope,norm_zero,add_zero] <;> ring

/-- An exact height identity, keeping every source, norm and prefix
factor. The two nonconstant height factors are definitionally identical. -/
private theorem raw_height_identity (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (w : ι→ℝ)
    (Bnorm Z ε δ κ t V v X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) (i : Fin 4) :
    rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κ t V v X Kfirst Kchild Cfirst ξfirst κpad W saving i=
    rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κ t V 0 X Kfirst Kchild Cfirst ξfirst κpad W saving i*
      (heightEnvelope v/heightEnvelope 0)^(2*componentDegree U i) := by
  have hp (j : ℕ) : heightEnvelope v^(2*j)=
      heightEnvelope 0^(2*j)*(heightEnvelope v/heightEnvelope 0)^(2*j) := by
    rw [←mul_pow]
    congr 1
    field_simp [(heightEnvelope_pos 0).ne']
  fin_cases i
  · simp [rawCosts,componentDegree]
  · change nonexceptionalCost U c s G Dart τ w Z ε δ κ t V v W=
      nonexceptionalCost U c s G Dart τ w Z ε δ κ t V 0 W*
        (heightEnvelope v/heightEnvelope 0)^(2*U.nonexceptionalDegree)
    unfold nonexceptionalCost fullCost fixedBudget
    rw [hp U.nonexceptionalDegree]
    ring
  · change reference τ G Gopp (sourceVolume s) Z*
      numericalCost s η G Dart Q U.exceptionalDegree U.exceptionalControl
        Bnorm ε δ ε δ c.kernel c.exceptional c.exceptionalSum c.exceptionalCount
        Z Kfirst Cfirst ξfirst κpad W v=
      (reference τ G Gopp (sourceVolume s) Z*
      numericalCost s η G Dart Q U.exceptionalDegree U.exceptionalControl
        Bnorm ε δ ε δ c.kernel c.exceptional c.exceptionalSum c.exceptionalCount
        Z Kfirst Cfirst ξfirst κpad W 0)*
        (heightEnvelope v/heightEnvelope 0)^(2*U.exceptionalDegree)
    unfold numericalCost
    have hbase (z : ℝ) : heightBase z=heightEnvelope z := rfl
    simp only [hbase]
    rw [hp U.exceptionalDegree]
    ring
  · simp [rawCosts,componentDegree]

private theorem raw_height_bound (U : Controls) (c : Constants) (s : Source ι a b)
    (η τ : Character) (G Gopp Dart Q : Id) (w : ι→ℝ)
    (Bnorm Z ε δ κ t V v X Kfirst Kchild Cfirst ξfirst κpad W saving : ℝ) (i : Fin 4)
    (h0 : 0≤rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κ t V 0 X
      Kfirst Kchild Cfirst ξfirst κpad W saving i) :
    rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κ t V v X Kfirst Kchild Cfirst ξfirst κpad W saving i≤
    rawCosts U c s η τ G Gopp Dart Q w Bnorm Z ε δ κ t V 0 X Kfirst Kchild Cfirst ξfirst κpad W saving i*
      (1+‖v‖)^(2*degree U) := by
  rw [raw_height_identity]
  apply mul_le_mul_of_nonneg_left _ h0
  have hi : componentDegree U i≤degree U := by
    fin_cases i <;> simp [componentDegree,degree]
  exact (pow_le_pow_left₀
    (div_nonneg (heightEnvelope_pos v).le (heightEnvelope_pos 0).le)
    (height_ratio_le v) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg v)) (by omega))

/-- Private analytic interface: its height premise is discharged by the
actual four suppliers in uniform_integrated_windows below. -/
private theorem actual_window_from_height (s : Source ι a b) (ha : 0<a)
    (C G seed D : Id) (hG : Supported G) (τ : Character)
    (K W : ℝ) (hK : 0<K) (hW : 0<W) (J : ℕ) (E : ℝ) (hE : 0≤E)
    (henergy : ∀v : ℝ,actualEnergy s ha C G hG seed D τ v K W≤E*(1+‖v‖)^(2*J))
    (right : Bool) (t θ X : ℝ) (hX : 0<X) :
    outputEnergy s ha C G seed D hG.1 τ t right logAnnulus X θ K W≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  have hf (θ : ℝ) :
      outputEnergy s ha C G seed D hG.1 τ t false logAnnulus X θ K W≤
        (windowBudget J t E*(1+‖θ‖)^J)^2 := by
    have hh := smoothed_window_energy_from_height logAnnulus logAnnulus_compact logAnnulus_smooth J
      Finset.univ (CenteredMomentFirstPhysicalSource.element C G hG.1 (sourceColumns s))
      (CenteredMomentFirstPhysicalSource.element_supported C G hG.1 (sourceColumns s))
      (fun I : Columns s C G hG.1=>originalResidual s ha seed G D I)
      τ t θ X hX ballProfile (16*K*W^4) (by positivity)
      (fun z=>ballProfile_nonneg _) (W*E) (mul_nonneg hW.le hE)
      (fun v=>by
        simp only [CenteredMomentFirstPhysicalSource.element_span]
        have hh := (div_le_iff₀ hW).mp (henergy v)
        exact hh.trans_eq (by ring))
    have hd := div_le_div_of_nonneg_right hh hW.le
    have he : outputEnergy s ha C G seed D hG.1 τ t false logAnnulus X θ K W≤
        (E*heightCost t θ^(2*J))*profileMoment J^2 := by
      convert hd using 1
      · simp only [outputEnergy,base,windowFactor,Bool.false_eq_true,if_false,
          CenteredMomentFirstPhysicalSource.element_span]
      · unfold profileMoment
        field_simp [hW.ne']
        <;> ring
    exact he.trans (shifted_window_budget J t θ E hE)
  cases right
  · exact hf θ
  · simpa only [outputEnergy,windowFactor,Bool.false_eq_true,if_false,if_true,
      star_logAnnulus_column,norm_neg] using hf (-θ)

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- The actual four-part estimates at every independent height, followed
by both column-window integrals and all sixteen component pairs. The
native exponent 3/4 comes from the original unconditional theorem.
The actual coefficient may retain the supplier avoidance mask. That
mask is removed only after the one genuine positive extraction; the
four numerical costs belong to the unavoided canonical source. There
is no child-energy, window-bound, or nonzero-block hypothesis.
All remaining inequalities are the original numerical geometry. -/
theorem uniform_integrated_windows
    (Wprofile : 𝓢(ℝ,ℂ)) (decay : ℕ)
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
      ε δ lo hi ξsecond saving : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b) (hMcap0 : 0<Mcap)
    (hL : 0≤L) (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hBR : 0≤BR) (hBG : 0≤BG) (hBH : 0≤BH) (hBsource : 0≤Bsource)
    (hPexp : 0≤Pexp) (hMgeom : 0≤Mgeom) (hBtail : 0≤Btail) (hBGtail : BG≤Btail)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap) (hε : 0<ε) (hδ : 0<δ)
    (hgap : (7/10:ℝ)+2*δ<1) (hξsecond : 0<ξsecond)
    (hMcap : Mgeom+(Bη+BG+ε)+Bsource+ε≤Mcap)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃U : Controls,∃Cpush Ckernel : ℝ,0<Cpush ∧ 0≤Ckernel ∧
    ∀η₀ : Character,Q≤η₀.modulus→∃c : Constants,
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t R₀ s→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
      sourceNormCap s.P b s.T s.d≤Z^Bsource→poolCap s≤Z^Btail→
      (∏i,s.P i)≤Z^Pexp→(s.Fhole.absNorm:ℝ)≤Z^BH→
    ∀cover : OriginalEnclosure s,∀(η : Character)(C D : Id)(hC : Supported C)(hD : Supported D),
      CompletedGauss.primeSupport C=CompletedGauss.primeSupport D→
      (η.modulus.absNorm:ℝ)≤Z^Bη→(C.absNorm:ℝ)≤Z^BG→(D.absNorm:ℝ)≤Z^BG→
    ∀(E : Finset (CommonIndex C D)),E∈inactiveSubsets C D→
    ∀(χ ξ : RayCharacter)(F : FixedPair η C D hC E χ ξ),
    ∀(Kfirst Tfirst Cfirst ξfirst κpad W : ℝ),0<Kfirst→0<W→1≤Cfirst→0≤ξfirst→
      Tfirst≤Cfirst*firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) Kfirst (sourceVolume s)→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    ∀Dart : Id,Squarefree Dart→Dart≠0→(Dart.absNorm:ℝ)≤Z^Btail→
    ∀(Tsecond X : ℝ),0≤Tsecond→Tsecond≤Z^(Mgeom-ξsecond)→
      1≤X→(2:ℝ)^Fintype.card ι*sourceNormCap s.P b s.T s.d≤X→
      X≤Z^Btail→W≤Z^Btail→W⁻¹≤Z^Btail→Tsecond≤Z^Btail→
    ∀n : ℤ,Retained (frequencyRadius Tfirst Z ξfirst) n→
    let KL:=nominalChildScale C D E Kfirst (sourceVolume s) Z κpad n
    let KR:=nominalChildScale D C (swapSubset C D E) Kfirst (sourceVolume s) Z κpad n
    KL≤Z^Btail→KR≤Z^Btail→X^2/(16*KL*W^4)≤Tsecond→X^2/(16*KR*W^4)≤Tsecond→
    let left:=rawCosts U c s η F.left C D Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KL Cfirst ξfirst κpad W saving
    let right:=rawCosts U c s η F.right D C Dart Q w (normExponent L Pexp ε)
      Z ε δ (3/4) t V 0 X Kfirst KR Cfirst ξfirst κpad W saving
    (∀i,0≤left i) ∧ (∀i,0≤right i) ∧
    ∀seed : Id,seed∣C→seed∣D→∀u : Id,u∣s.R*C→u∣s.R*D→
    let sActual:=avoidSource s u
    ∀(tleft tright XL XR : ℝ),0<XL→0<XR→
    let cost:=∑i : Fin 4,∑j : Fin 4,windowBudget (degree U) tleft (left i)*
      windowBudget (degree U) tright (right j)
    (∀windowθ : ℝ,
      Real.sqrt (outputEnergy sActual ha D C seed Dart hC.1 F.left tleft false logAnnulus XL windowθ KL W)*
      Real.sqrt (outputEnergy sActual ha C D seed Dart hD.1 F.right tright true logAnnulus XR windowθ KR W)≤
        cost*(1+‖windowθ‖)^(2*degree U)) ∧
    ∀(Ds : Finset Id)(rows : Finset O),
      (∀Dsel∈Ds,Supported Dsel)→(∀z∈rows,z≠0)→
    ∀(weight : Id→ℝ)(mass : ℝ),0≤mass→
      (∀Dsel∈Ds,0≤weight Dsel∧weight Dsel≤mass)→
      (∀Dsel∈Ds,(Dsel.absNorm:ℝ)≤2*W)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KL)→
      (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤KR)→
    let cleft:=rowVector sActual ha D C seed Dart hC.1 F.left tleft weight W false
    let cright:=rowVector sActual ha C D seed Dart hD.1 F.right tright weight W true
    let uleft:=fun I : Columns sActual D C hC.1=>Real.log ((I.val.absNorm:ℝ)/XL)
    let uright:=fun I : Columns sActual C D hD.1=>Real.log ((I.val.absNorm:ℝ)/XR)
    (∀windowθ : ℝ,
      Real.sqrt (∑p∈Ds×ˢrows,‖leftColumn Finset.univ (cleft p) logAnnulus uleft windowθ‖^2)*
      Real.sqrt (∑p∈Ds×ˢrows,‖rightColumn Finset.univ (cright p) logAnnulus uright windowθ‖^2)≤
        (pushCost Cpush mass KL KR W ε*cost)*(1+‖windowθ‖)^(2*degree U)) ∧
    ∀(ρ x : Id×O→ℝ)(phase : Id×O→ℂ),(∀p∈Ds×ˢrows,‖phase p‖≤1)→
    ∀Rwindow : ℝ,0<Rwindow→
      (1+Rwindow)^decay*‖∑p∈Ds×ˢrows,phase p*
        ∑I : Columns sActual D C hC.1,∑J : Columns sActual C D hD.1,
          (cleft p I*star (cright p J))*
          wholeKernel Wprofile (fun _=>logAnnulus) Rwindow (ρ p) (x p) (uleft I) (uright J)‖≤
      Ckernel*(pushCost Cpush mass KL KR W ε*cost) := by
  obtain ⟨U,hfull⟩ := uniform_full_budget (ι:=ι) M Hray hHray N Holes hcard Wslot
    a b Mcap L Lslot Lcap Cap BR BG BH Bsource Bη Pexp Mgeom Btail
    ε δ lo hi (3/4) ξsecond saving hWs hW ha haUpper hb hMcap0
    hL hLslot hLcap hCap hBR hBG hBH hBsource hPexp hMgeom hBtail hBGtail
    hCapb hLordinary hε hδ hgap hξsecond hMcap hβ IncumbentInput.native_kappa_bound
    Q hQt hQ72 hQM
  obtain ⟨Cpush,hCpush,htransfer⟩ :=
    paired_fourier_row_transfer (ι:=ι) (a:=a) (b:=b) ε hε
  obtain ⟨Ckernel,hCkernel,hkernel⟩ := whole_kernel_row_estimate Wprofile
    (fun _=>logAnnulus) (fun _=>Real.log 4)
    (fun _=>Real.log_nonneg (by norm_num))
    (fun _ x hx=>by
      have hh:=logAnnulus_support hx
      exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩)
    decay (2*degree U)
  refine ⟨U,Cpush,Ckernel,hCpush,hCkernel,?_⟩
  intro η₀ hη₀
  obtain ⟨c,hfull⟩ := hfull η₀ hη₀
  refine ⟨c,?_⟩
  filter_upwards [hfull] with Z hz
  obtain ⟨hZ,hfull⟩ := hz
  refine ⟨hZ,?_⟩
  intro θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hR hH hholes hHR
    hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover η C D hC hD hCD hη hCcap hDcap
    E hE χ ξ F Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Dart hDart hDart0 hDartCap Tsecond X hT hTcap
    hX hXcap hXupper hWupper hWinv hTupper n hret KL KR hKLcap hKRcap hTL hTR left right
  have hdata (v₁ v₂ : ℝ) := hfull θ w σ freq t V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ hsource hpool hP hF cover
    η C D hC hD hCD hη hCcap hDcap E hE χ ξ F
    Kfirst Tfirst Cfirst ξfirst κpad W hKfirst hWblock hCfirst hξfirst hfirst
    χ₀ msecond hm hml hm2 Dart hDart hDart0 hDartCap v₁ v₂ Tsecond X hT hTcap
    hX hXcap hXupper hWupper hWinv hTupper n hret hKLcap hKRcap hTL hTR
  have hl0 (i : Fin 4) : 0≤left i :=
    (components_nonneg s ha (zero_le_one.trans hb) cover C Dart F.left 0 KL W
      Tsecond Z ξsecond Q msecond χ₀ i).trans ((hdata 0 0).1 i)
  have hr0 (i : Fin 4) : 0≤right i :=
    (components_nonneg s ha (zero_le_one.trans hb) cover D Dart F.right 0 KR W
      Tsecond Z ξsecond Q msecond χ₀ i).trans ((hdata 0 0).2.1 i)
  refine ⟨hl0,hr0,?_⟩
  intro seed hseedC hseedD u huC huD sActual tleft tright XL XR hXL hXR cost
  have hKL : 0<KL := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hKR : 0<KR := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hleft (v : ℝ) : actualEnergy sActual ha D C hC seed Dart F.left v KL W≤
      (∑i,left i)*(1+‖v‖)^(2*degree U) := by
    apply (avoided_actual_energy_four_parts s ha (zero_le_one.trans hb) cover u D C seed Dart
      hD hC hCD.symm hseedC huC F.left v KL W Tsecond Z ξsecond hKL hWblock Q msecond χ₀).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    exact ((hdata v 0).1 i).trans (raw_height_bound U c s η F.left C D Dart Q w
      (normExponent L Pexp ε) Z ε δ (3/4) t V v X Kfirst KL Cfirst ξfirst κpad W saving i (hl0 i))
  have hright (v : ℝ) : actualEnergy sActual ha C D hD seed Dart F.right v KR W≤
      (∑i,right i)*(1+‖v‖)^(2*degree U) := by
    apply (avoided_actual_energy_four_parts s ha (zero_le_one.trans hb) cover u C D seed Dart
      hC hD hCD hseedD huD F.right v KR W Tsecond Z ξsecond hKR hWblock Q msecond χ₀).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    exact ((hdata 0 v).2.1 i).trans (raw_height_bound U c s η F.right D C Dart Q w
      (normExponent L Pexp ε) Z ε δ (3/4) t V v X Kfirst KR Cfirst ξfirst κpad W saving i (hr0 i))
  have hwindow (windowθ : ℝ) :
      Real.sqrt (outputEnergy sActual ha D C seed Dart hC.1 F.left tleft false logAnnulus XL windowθ KL W)*
      Real.sqrt (outputEnergy sActual ha C D seed Dart hD.1 F.right tright true logAnnulus XR windowθ KR W)≤
        cost*(1+‖windowθ‖)^(2*degree U) := by
    have hl := actual_window_from_height sActual ha D C seed Dart hC F.left KL W hKL hWblock
      (degree U) (∑i,left i) (Finset.sum_nonneg (fun i _=>hl0 i)) hleft false tleft windowθ XL hXL
    have hr := actual_window_from_height sActual ha C D seed Dart hD F.right KR W hKR hWblock
      (degree U) (∑i,right i) (Finset.sum_nonneg (fun i _=>hr0 i)) hright true tright windowθ XR hXR
    have hlroot := Real.sqrt_le_sqrt hl
    have hrroot := Real.sqrt_le_sqrt hr
    have hlpos : 0≤windowBudget (degree U) tleft (∑i,left i)*(1+‖windowθ‖)^(degree U) :=
      mul_nonneg (windowBudget_nonneg _ _ _) (by positivity)
    have hrpos : 0≤windowBudget (degree U) tright (∑i,right i)*(1+‖windowθ‖)^(degree U) :=
      mul_nonneg (windowBudget_nonneg _ _ _) (by positivity)
    rw [Real.sqrt_sq hlpos] at hlroot
    rw [Real.sqrt_sq hrpos] at hrroot
    have hp := mul_le_mul hlroot hrroot (Real.sqrt_nonneg _) hlpos
    have hpair' : windowBudget (degree U) tleft (∑i,left i)*windowBudget (degree U) tright (∑i,right i)≤
        cost := by
      have hs := mul_le_mul (windowBudget_sum Finset.univ left (fun i _=>hl0 i) (degree U) tleft)
        (windowBudget_sum Finset.univ right (fun i _=>hr0 i) (degree U) tright)
        (windowBudget_nonneg _ _ _) (Finset.sum_nonneg (fun i _=>windowBudget_nonneg _ _ _))
      exact hs.trans_eq (by rw [Finset.sum_mul]; simp only [cost,Finset.mul_sum])
    calc
      _≤(windowBudget (degree U) tleft (∑i,left i)*windowBudget (degree U) tright (∑i,right i))*
          (1+‖windowθ‖)^(2*degree U) := hp.trans_eq (by
            rw [show 2*degree U=degree U*2 by omega,pow_mul]
            ring)
      _≤_ := mul_le_mul_of_nonneg_right hpair' (by positivity)
  refine ⟨hwindow,?_⟩
  intro Ds rows hDs hrows weight mass hmass hweight hDN hKLrows hKRrows
    cleft cright uleft uright
  have hcost : 0≤cost := Finset.sum_nonneg (fun i _=>Finset.sum_nonneg
    (fun j _=>mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _)))
  have hpush : 0≤pushCost Cpush mass KL KR W ε :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hfourier (windowθ : ℝ) :
      Real.sqrt (∑p∈Ds×ˢrows,‖leftColumn Finset.univ (cleft p) logAnnulus uleft windowθ‖^2)*
      Real.sqrt (∑p∈Ds×ˢrows,‖rightColumn Finset.univ (cright p) logAnnulus uright windowθ‖^2)≤
        (pushCost Cpush mass KL KR W ε*cost)*(1+‖windowθ‖)^(2*degree U) := by
    have ht := htransfer sActual ha C D seed Dart hC.1 hD.1 F.left F.right tleft tright
      Ds rows hDs hrows weight W KL KR mass hWblock hKL hKR hmass hweight hDN hKLrows hKRrows
      logAnnulus logAnnulus XL XR windowθ
    have hAL : 0≤mass*Cpush*(16*KL*W^4)^ε :=
      mul_nonneg (mul_nonneg hmass hCpush.le) (Real.rpow_nonneg (by positivity) _)
    have hAR : 0≤mass*Cpush*(16*KR*W^4)^ε :=
      mul_nonneg (mul_nonneg hmass hCpush.le) (Real.rpow_nonneg (by positivity) _)
    calc
      _≤Real.sqrt (mass*Cpush*(16*KL*W^4)^ε*
          outputEnergy sActual ha D C seed Dart hC.1 F.left tleft false logAnnulus XL windowθ KL W)*
        Real.sqrt (mass*Cpush*(16*KR*W^4)^ε*
          outputEnergy sActual ha C D seed Dart hD.1 F.right tright true logAnnulus XR windowθ KR W) := ht
      _=pushCost Cpush mass KL KR W ε*
        (Real.sqrt (outputEnergy sActual ha D C seed Dart hC.1 F.left tleft false logAnnulus XL windowθ KL W)*
        Real.sqrt (outputEnergy sActual ha C D seed Dart hD.1 F.right tright true logAnnulus XR windowθ KR W)) := by
          rw [Real.sqrt_mul hAL,Real.sqrt_mul hAR]
          unfold pushCost
          ring
      _≤pushCost Cpush mass KL KR W ε*(cost*(1+‖windowθ‖)^(2*degree U)) :=
        mul_le_mul_of_nonneg_left (hwindow windowθ) hpush
      _=_ := by ring
  refine ⟨hfourier,?_⟩
  intro ρ x phase hphase Rwindow hRwindow
  exact hkernel Rwindow hRwindow (Ds×ˢrows) Finset.univ Finset.univ
    cleft cright uleft uright ρ x phase hphase
    (fun p _=>logAnnulus_norm _) (fun p _=>logAnnulus_norm _)
    (pushCost Cpush mass KL KR W ε*cost) (mul_nonneg hpush hcost) hfourier

end
end Candidate.FourthPower.MixedFirstIntegratedWindows

