/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Colored first summed window and joint kernel, following Sil CF section 4. -/
import Candidate.C092.transport.TwistedRawBallAllocation
import Submissions.sil_density_split_20261026.CubeFree.First.JointKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy CenteredMomentSecondHeightFamily
open CenteredMomentSmoothedWindowEnergy CenteredMomentSecondWindowBudget CenteredMomentSecondWindowSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentFirstColumns CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondIdealBlockBound
open QRH.SilDensitySplit.CubeFree
open FP.MixedPrincipalPair FP.MixedPrincipalWindow FP.MixedFirstAveragedWindow
open FP.MixedFirstPhysicalApplication FP.MixedOriginalSecondZero
open QRH.SilDensitySplit.CubeFree.First
open ActualEisensteinCubic CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance c092LocalInst_Candidate_C092_transport_TwistedRawBallKernel_05ebb1577d906d15_001 {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def base (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (I : Columns s C G hG) : ℂ :=
  rawCoefficient s ha ω₁ ω₂ seed G D I*heightCoeff τ t I

def selectedRow (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (right : Bool) (V : ℝ→ℂ) (X θ : ℝ) (F : Id) (z : O) : ℂ :=
  ∑I : Columns s C G hG,
    base s ha ω₁ ω₂ C G seed D hG τ t I*
      windowFactor right V (Real.log ((I.val.absNorm:ℝ)/X)) θ*
      (idealRowHom (primaryGenerator F) I.val)^2*
      gaussRow (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s) I)
        (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s) I) z

def rowVector (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (reflect : Bool)
    (p : Id×O) (I : Columns s C G hG) : ℂ :=
  (Real.sqrt (w p.1/W):ℂ)*base s ha ω₁ ω₂ C G seed D hG τ t I*
    (idealRowHom (primaryGenerator p.1) I.val)^2*
    gaussRow (CenteredMomentFirstPhysicalSource.element C G hG (sourceColumns s) I)
      (CenteredMomentFirstPhysicalSource.element_supported C G hG (sourceColumns s) I)
      (if reflect then -p.2 else p.2)

theorem left_column (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (V : ℝ→ℂ) (X θ : ℝ) (p : Id×O) :
    leftColumn Finset.univ (rowVector s ha ω₁ ω₂ C G seed D hG τ t w W false p) V
      (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ=
    (Real.sqrt (w p.1/W):ℂ)*selectedRow s ha ω₁ ω₂ C G seed D hG τ t false V X θ p.1 p.2 := by
  simp only [leftColumn,rowVector,selectedRow,windowFactor,Bool.false_eq_true,
    if_false,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem right_column (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C G seed D : Id) (hG : G≠0)
    (τ : Character) (t : ℝ) (w : Id→ℝ) (W : ℝ) (V : ℝ→ℂ) (X θ : ℝ) (p : Id×O) :
    rightColumn Finset.univ (rowVector s ha ω₁ ω₂ C G seed D hG τ t w W true p) V
      (fun I : Columns s C G hG=>Real.log ((I.val.absNorm:ℝ)/X)) θ=
    (Real.sqrt (w p.1/W):ℂ)*star (selectedRow s ha ω₁ ω₂ C G seed D hG τ t true V X θ p.1 (-p.2)) := by
  simp only [rightColumn,rowVector,selectedRow,windowFactor,if_true,
    star_sum,star_mul,star_star,Finset.mul_sum,Complex.star_def,map_mul,map_pow,
    Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [←Complex.star_def,star_star]
  ring


/-! ### Raw energies and windows (forked cube-free columns) -/

def windowPolynomial (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id) (hG : G ≠ 0)
    (u : Id) (τ : Character) (right : Bool) (t θ X : ℝ) (z : O) : ℂ :=
  gaussPolynomial Finset.univ (element opposite G hG (sourceColumns s))
    (element_supported opposite G hG (sourceColumns s))
    (fun I : columns opposite G hG (sourceColumns s) =>
      rawCoefficient s ha ω₁ ω₂ 1 G u I*heightCoeff τ t I*
        windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z

theorem selected_one_window (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id) (hG : G ≠ 0)
    (u : Id) (τ : Character) (right : Bool) (t θ X : ℝ) (z : O) :
    selectedRow s ha ω₁ ω₂ opposite G 1 u hG τ t right logAnnulus X θ 1 z =
      windowPolynomial s ha ω₁ ω₂ opposite G hG u τ right t θ X z := by
  unfold selectedRow base windowPolynomial gaussPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  have hs : Supported I.val := by
    simpa only [element_span] using element_supported opposite G hG (sourceColumns s) I
  simp only [primaryGenerator_one, idealRowHom_one_supported I.val hs, one_pow, mul_one]

theorem window_conj (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id) (hG : G ≠ 0)
    (u : Id) (τ : Character) (t θ X : ℝ) (z : O) :
    windowPolynomial s ha ω₁ ω₂ opposite G hG u τ true t θ X z =
      windowPolynomial s ha ω₁ ω₂ opposite G hG u τ false t (-θ) X z := by
  simp only [windowPolynomial, windowFactor, Bool.false_eq_true, ↓reduceIte,
    star_logAnnulus_column]

theorem finite_window_le_energy (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id)
    (hG : G ≠ 0) (u : Id) (τ : Character) (right : Bool) (t θ X K : ℝ) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ K) :
    (∑ z ∈ rows, ‖windowPolynomial s ha ω₁ ω₂ opposite G hG u τ right t θ X z‖^2) ≤
      (gaussEnergy Finset.univ (element opposite G hG (sourceColumns s))
        (element_supported opposite G hG (sourceColumns s))
        (fun I : columns opposite G hG (sourceColumns s) =>
          rawCoefficient s ha ω₁ ω₂ 1 G u I*heightCoeff τ t I*
            windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
        ballProfile K).re := by
  have hb := finite_weighted_le_gaussEnergy Finset.univ
    (element opposite G hG (sourceColumns s)) (element_supported opposite G hG (sourceColumns s))
    (fun I : columns opposite G hG (sourceColumns s) =>
      rawCoefficient s ha ω₁ ω₂ 1 G u I*heightCoeff τ t I*
        windowFactor right logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
    ballProfile K hK (fun z => ballProfile_nonneg _) rows
  have hm (z : O) (hz : z ∈ rows) : ballProfile (‖eisEmbedding z‖^2/K) = 1 :=
    ballProfile_one _ (div_nonneg (sq_nonneg _) hK.le) ((div_le_one hK).mpr (hrows z hz))
  have heq : (∑ z ∈ rows, ‖windowPolynomial s ha ω₁ ω₂ opposite G hG u τ right t θ X z‖^2) =
      ∑ z ∈ rows, ‖windowPolynomial s ha ω₁ ω₂ opposite G hG u τ right t θ X z‖^2*
        (ballProfile (‖eisEmbedding z‖^2/K)).re := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hm z hz, Complex.one_re, mul_one]
  rw [heq]
  exact hb

/-- The summed window bound: a bound on `∑_u` of the raw height energies bounds `∑_u ∑_z`
of the (ordinary) window polynomials on the `K`-ball rows. -/
theorem summed_window_bound (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id) (hG : Supported G)
    (Us : Finset Id) (τ : Character) (t θ X K : ℝ) (hX : 0 < X) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ K)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J)) :
    (∑ u ∈ Us, ∑ z ∈ rows, ‖windowPolynomial s ha ω₁ ω₂ opposite G hG.1 u τ false t θ X z‖^2) ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  have he := summed_window_energy_from_height logAnnulus logAnnulus_compact logAnnulus_smooth
    J Us Finset.univ (element opposite G hG.1 (sourceColumns s))
    (element_supported opposite G hG.1 (sourceColumns s))
    (fun u (I : columns opposite G hG.1 (sourceColumns s)) => rawCoefficient s ha ω₁ ω₂ 1 G u I)
    τ t θ X hX ballProfile K hK (fun z => ballProfile_nonneg _) E hE
    (fun v => by simpa only [rawEnergy, element_span] using hraw v)
  have he' : (∑ u ∈ Us, (gaussEnergy Finset.univ (element opposite G hG.1 (sourceColumns s))
        (element_supported opposite G hG.1 (sourceColumns s))
        (fun I : columns opposite G hG.1 (sourceColumns s) =>
          rawCoefficient s ha ω₁ ω₂ 1 G u I*heightCoeff τ t I*
            windowFactor false logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
        ballProfile K).re) ≤ (E*heightCost t θ^(2*J))*profileMoment J^2 := by
    simpa only [windowFactor, Bool.false_eq_true, ↓reduceIte, element_span, profileMoment] using he
  calc
    _ ≤ ∑ u ∈ Us, (gaussEnergy Finset.univ (element opposite G hG.1 (sourceColumns s))
        (element_supported opposite G hG.1 (sourceColumns s))
        (fun I : columns opposite G hG.1 (sourceColumns s) =>
          rawCoefficient s ha ω₁ ω₂ 1 G u I*heightCoeff τ t I*
            windowFactor false logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)
        ballProfile K).re :=
      Finset.sum_le_sum (fun u _ =>
        finite_window_le_energy s ha ω₁ ω₂ opposite G hG.1 u τ false t θ X K hK rows hrows)
    _ ≤ _ := he'
    _ ≤ _ := shifted_window_budget J t θ E hE

theorem summed_left_column_bound (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id)
    (hG : Supported G) (Us : Finset Id) (τ : Character) (t θ X K : ℝ) (hX : 0 < X) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ K)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J)) :
    (∑ u ∈ Us, ∑ z ∈ rows, ‖leftColumn Finset.univ
      (rowVector s ha ω₁ ω₂ opposite G 1 u hG.1 τ t (fun _ => 1) 1 false (1,z)) logAnnulus
      (fun I : Columns s opposite G hG.1 => Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2) ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simp only [left_column, one_div, inv_one, Real.sqrt_one, Complex.ofReal_one, one_mul,
    selected_one_window]
  exact summed_window_bound s ha ω₁ ω₂ opposite G hG Us τ t θ X K hX hK rows hrows J E hE hraw

theorem summed_right_column_bound (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (opposite G : Id)
    (hG : Supported G) (Us : Finset Id) (τ : Character) (t θ X K : ℝ) (hX : 0 < X) (hK : 0 < K)
    (rows : Finset O) (hrows : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ K)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hraw : ∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ opposite G hG u τ v K ≤ E*(1+‖v‖)^(2*J)) :
    (∑ u ∈ Us, ∑ z ∈ rows, ‖rightColumn Finset.univ
      (rowVector s ha ω₁ ω₂ opposite G 1 u hG.1 τ t (fun _ => 1) 1 true (1,z)) logAnnulus
      (fun I : Columns s opposite G hG.1 => Real.log ((I.val.absNorm:ℝ)/X)) θ‖^2) ≤
      (windowBudget J t E*(1+‖θ‖)^J)^2 := by
  simp only [right_column, one_div, inv_one, Real.sqrt_one, Complex.ofReal_one, one_mul, norm_star,
    selected_one_window, window_conj]
  have hneg : ∀ z ∈ rows.image Neg.neg, ‖eisEmbedding z‖^2 ≤ K := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    simpa only [map_neg, norm_neg] using hrows y hy
  have hb := summed_window_bound s ha ω₁ ω₂ opposite G hG Us τ t (-θ) X K hX hK (rows.image Neg.neg)
    hneg J E hE hraw
  rw [norm_neg] at hb
  calc
    _ = ∑ u ∈ Us, ∑ z ∈ rows.image Neg.neg,
        ‖windowPolynomial s ha ω₁ ω₂ opposite G hG.1 u τ false t (-θ) X z‖^2 :=
      Finset.sum_congr rfl (fun u _ =>
        (Finset.sum_image (fun x _ y _ h => neg_injective h)).symm)
    _ ≤ _ := hb

/-- The paired column bound on the JOINT rows `Us ×ˢ rows`. -/
theorem summed_paired_column_bound (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (Us : Finset Id) (τL τR : Character)
    (t θ A₀ B₀ KL KR : ℝ) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) (hKL : 0 < KL) (hKR : 0 < KR)
    (rows : Finset O) (hrowsL : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL)
    (hrowsR : ∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR)
    (J : ℕ) (EL ER : ℝ) (hEL : 0 ≤ EL) (hER : 0 ≤ ER)
    (hleft : ∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ D C hC u τL v KL ≤ EL*(1+‖v‖)^(2*J))
    (hright : ∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ C D hD u τR v KR ≤ ER*(1+‖v‖)^(2*J)) :
    Real.sqrt (∑ k ∈ Us ×ˢ rows, ‖leftColumn Finset.univ
      (rowVector s ha ω₁ ω₂ D C 1 k.1 hC.1 τL t (fun _ => 1) 1 false (1,k.2)) logAnnulus
      (fun I : Columns s D C hC.1 => Real.log ((I.val.absNorm:ℝ)/A₀)) θ‖^2)*
    Real.sqrt (∑ k ∈ Us ×ˢ rows, ‖rightColumn Finset.univ
      (rowVector s ha ω₁ ω₂ C D 1 k.1 hD.1 τR t (fun _ => 1) 1 true (1,k.2)) logAnnulus
      (fun I : Columns s C D hD.1 => Real.log ((I.val.absNorm:ℝ)/B₀)) θ‖^2) ≤
      (windowBudget J t EL*windowBudget J t ER)*(1+‖θ‖)^(2*J) := by
  have hl := summed_left_column_bound s ha ω₁ ω₂ D C hC Us τL t θ A₀ KL hA₀ hKL rows hrowsL J EL hEL hleft
  have hr := summed_right_column_bound s ha ω₁ ω₂ C D hD Us τR t θ B₀ KR hB₀ hKR rows hrowsR J ER hER
    hright
  rw [Finset.sum_product, Finset.sum_product]
  have hLp : 0 ≤ windowBudget J t EL*(1+‖θ‖)^J :=
    mul_nonneg (windowBudget_nonneg _ _ _) (pow_nonneg (by positivity) _)
  have hRp : 0 ≤ windowBudget J t ER*(1+‖θ‖)^J :=
    mul_nonneg (windowBudget_nonneg _ _ _) (pow_nonneg (by positivity) _)
  have hLs := Real.sqrt_le_iff.mpr ⟨hLp, hl⟩
  have hRs := Real.sqrt_le_iff.mpr ⟨hRp, hr⟩
  apply (mul_le_mul hLs hRs (Real.sqrt_nonneg _) hLp).trans_eq
  rw [show 2*J = J*2 by omega, pow_mul]
  ring

/-! ### The joint kernel estimate -/

def weightedPair (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id → ℂ) (C D seed L : Id)
    (hC : C≠0) (hD : D≠0) (τ₁ τ₂ : Character) (t₁ t₂ : ℝ)
    (w : Id→ℝ) (W : ℝ) (p : Id×O) (kernel : Id→Id→ℂ) : ℂ :=
  ∑I : Columns s D C hC,∑J : Columns s C D hD,
    (rowVector s ha ω₁ ω₂ D C seed L hC τ₁ t₁ w W false p I*
      star (rowVector s ha ω₁ ω₂ C D seed L hD τ₂ t₂ w W true p J))*kernel I J


/-- FP `RepairedFirstRawKernel.matrix` (verbatim body, forked columns). -/
def rawMatrix (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (E : Finset (CommonIndex C D)) (u : Id) (τL τR : Character) (t : ℝ)
    (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  ∑ z ∈ rows, commonPhase C D hC (1,z)*
    weightedPair s ha ω₁ ω₂ C D 1 u hC.1 hD.1 τL τR t t (fun _ => 1) 1 (1,z)
      (physicalKernel Φ (fun _ => logAnnulus) C D E K K₀ H₀ A₀ B₀ z)

/-- The Möbius-weighted artificial-divisor sum of the raw matrices, kept as ONE sum. -/
def summedMatrix (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id → ℂ) (C D : Id) (hC : Supported C)
    (hD : Supported D) (E : Finset (CommonIndex C D)) (Us : Finset Id) (τL τR : Character)
    (t : ℝ) (rows : Finset O) (Φ : 𝓢(ℝ,ℂ)) (K K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  ∑ u ∈ Us, (UniqueFactorizationMonoid.moebius u : ℂ)*
    rawMatrix s ha ω₁ ω₂ C D hC hD E u τL τR t rows Φ K K₀ H₀ A₀ B₀

set_option maxHeartbeats 800000 in
/-- Joint-row kernel estimate (CF §4): the kernel constant is chosen before the source, the
radii, the common ideals, the profiles and the divisor set `Us`; the ONLY analytic input is
the pair of SUMMED raw side bounds. No `1/N(u)` weight and no artificial mass appear. -/
theorem summed_kernel_from_raw (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, ∀ ω₁ ω₂ : Id → ℂ,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (Us : Finset Id) (τL τR : Character) (t K K₀ H₀ A₀ B₀ KL KR : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR →
    ∀ rows : Finset O, (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
    ∀ EL ER : ℝ, 0 ≤ EL → 0 ≤ ER →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ D C hC u τL v KL ≤ EL*(1+‖v‖)^(2*J)) →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ C D hD u τR v KR ≤ ER*(1+‖v‖)^(2*J)) →
      ‖summedMatrix s ha ω₁ ω₂ C D hC hD E Us τL τR t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t EL*windowBudget J t ER) := by
  obtain ⟨Ckernel, hCkernel, hkernel⟩ := whole_kernel_row_estimate Φ (fun _ => logAnnulus)
    (fun _ => Real.log 4) (fun _ => Real.log_nonneg (by norm_num))
    (fun _ y hy => logAnnulus_enclosure y hy) 0 (2*J)
  refine ⟨Ckernel, hCkernel, ?_⟩
  intro s ha ω₁ ω₂ C D hC hD E Us τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrowsL
    hrowsR EL ER hEL hER hl hr
  have hRwin : 0 < K₀*H₀/(A₀*B₀) := div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀)
  have he := hkernel (K₀*H₀/(A₀*B₀)) hRwin (Us ×ˢ rows) Finset.univ Finset.univ
    (fun k : Id × O => rowVector s ha ω₁ ω₂ D C 1 k.1 hC.1 τL t (fun _ => 1) 1 false (1,k.2))
    (fun k : Id × O => rowVector s ha ω₁ ω₂ C D 1 k.1 hD.1 τR t (fun _ => 1) 1 true (1,k.2))
    (fun I : Columns s D C hC.1 => Real.log ((I.val.absNorm:ℝ)/A₀))
    (fun I : Columns s C D hD.1 => Real.log ((I.val.absNorm:ℝ)/B₀))
    (fun _ : Id × O => Real.log (((K/‖eisEmbedding (primeSubsetGenerator
      (fun P : CommonIndex C D => P.val) E)‖^2)/‖eisEmbedding (activeConductor C D)‖^2)/K₀))
    (fun k : Id × O => Real.log (‖eisEmbedding k.2‖^2/H₀))
    (fun k : Id × O => (UniqueFactorizationMonoid.moebius k.1 : ℂ)*commonPhase C D hC (1,k.2))
    (fun k _ => by
      rw [norm_mul]
      exact (mul_le_mul (QuadraticInitialBound.norm_ideal_moebius_le_one k.1)
        (commonPhase_norm C D hC (1,k.2)) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (fun k _ => logAnnulus_norm _) (fun k _ => logAnnulus_norm _)
    (windowBudget J t EL*windowBudget J t ER)
    (mul_nonneg (windowBudget_nonneg _ _ _) (windowBudget_nonneg _ _ _))
    (fun θ => summed_paired_column_bound s ha ω₁ ω₂ C D hC hD Us τL τR t θ A₀ B₀ KL KR hA₀ hB₀ hKL hKR
      rows hrowsL hrowsR J EL ER hEL hER hl hr)
  rw [pow_zero, one_mul] at he
  refine le_of_eq_of_le ?_ he
  congr 1
  simp only [summedMatrix, rawMatrix, weightedPair, physicalKernel, Finset.sum_product,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun z _ =>
    Finset.sum_congr rfl (fun I _ => Finset.sum_congr rfl (fun J _ => ?_))))
  ring


#print axioms summed_window_bound
#print axioms summed_kernel_from_raw
end
end QRH.Cycle092.TwistedRawBall
