/- Copyright (c) 2026 Sil. Apache-2.0.
Exact finite application of the first physical block to the selected-divisor
row family.  No moment estimate is assumed here.  The common source can be
the actual avoided source; only IntegratedWindows needs its canonical parent.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstAveragedWindow
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstTwistedReference
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstPhysicalApplication
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily ActualEisensteinCubic
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ConcreteTraceCRT CenteredMomentLattice CenteredMomentLiveDomain
open RayFourExpansion FourierBridge CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentGaussEnergy CenteredMomentSmooth
open CenteredMomentChildAssembly CenteredMomentFirstAssembly CenteredMomentFirstColumns
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentMobiusRegroup CenteredMomentFirstSectorTransform CenteredMomentSecondSectorColumns
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalSecondZero
open MixedOriginalCoprimality MixedHeightEnergy MixedFirstAveragedWindow
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def selectedTwist (F I : Id) : ℂ := (idealRowHom (primaryGenerator F) I)^2

theorem selectedTwist_mul (F I J : Id) :
    selectedTwist F (I*J)=selectedTwist F I*selectedTwist F J := by
  simp only [selectedTwist,map_mul,mul_pow]

theorem selectedTwist_norm (F I : Id) : ‖selectedTwist F I‖≤1 := by
  rw [selectedTwist,norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (idealRowHom_norm _ _) 2).trans_eq (by norm_num)

def selectedCoefficient (s : Source ι a b) (ha : 0<a) (seed F I : Id) : ℂ :=
  sourceCoefficient s ha seed I*selectedTwist F I

theorem selected_support (s : Source ι a b) (ha : 0<a) (seed F I : Id)
    (h : selectedCoefficient s ha seed F I≠0) : sourceCoefficient s ha seed I≠0 :=
  (mul_ne_zero_iff.mp h).1

/-- The original first-sector height stays outside every selected-divisor
average.  In particular it is not discarded when fixed common labels vanish. -/
def commonHeight (s : Source ι a b) (η : Character) (t : ℝ) (C D : Id) : ℂ :=
  rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t C*
    star (rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t D)

/-- Source-aware FixedPair column identity, before any absolute values or
Fourier estimates.  Both the common and residual selected twists remain. -/
theorem selected_divisor_column (s : Source ι a b) (ha : 0<a)
    (seed F G L I : Id) (hI : Supported I) (η τ : Character)
    (ψ : O→ℂ) (ξ : RayCharacter)
    (hτ : ∀J : Id,Supported J→∀t : ℝ,
      heightCoeff τ t J=rowWeight η fixedBadMask 1 1 t J*
        (ψ (primaryGenerator J)*rayCharacter ξ (primaryGenerator J))) (t : ℝ) :
    divisorCoefficient L (fun J : Id=>primaryGenerator J)
      (fun J=>selectedCoefficient s ha seed F (G*J)*
        rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*ψ (primaryGenerator J)) ξ I=
      selectedTwist F G*(originalResidual s ha seed G L I*heightCoeff τ t I)*
        selectedTwist F I := by
  have hh := original_divisor_column s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    b s.X₁ s.X₂ s.Y₁ s.Y₂ η τ ψ ξ hτ G L I hI t
  change divisorCoefficient L (fun J : Id=>primaryGenerator J)
      (fun J=>sourceCoefficient s ha seed (G*J)*
        rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*ψ (primaryGenerator J)) ξ I=
    originalResidual s ha seed G L I*heightCoeff τ t I at hh
  unfold divisorCoefficient at hh ⊢
  rw [primary_span_supported I hI] at hh ⊢
  by_cases hd : L∣I
  · simp only [if_pos hd] at hh ⊢
    rw [selectedCoefficient,selectedTwist_mul]
    calc
      _=selectedTwist F G*
          (sourceCoefficient s ha seed (G*I)*
            rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t I*
              ψ (primaryGenerator I)*rayCharacter ξ (primaryGenerator I))*selectedTwist F I := by ring
      _=_ := by rw [hh]
  · simp only [if_neg hd,originalResidual] at hh ⊢
    simp only [if_neg hd,zero_mul,mul_zero]

private theorem columns_same_support (Q Q' G : Id) (hG : G≠0)
    (S : Finset Id) (hQ : Q≠0) (hQ' : Q'≠0)
    (hQQ' : primeSupport Q=primeSupport Q') :
    columns Q G hG S=columns Q' G hG S := by
  ext I
  simp only [columns,Finset.mem_filter]
  constructor
  · rintro ⟨hI,hcop⟩
    have hs := residualPool_supported G hG S ⟨I,hI⟩
    exact ⟨hI,(coprime_of_same_support Q Q' I hQ hQ' hs.1 hQQ').mp hcop⟩
  · rintro ⟨hI,hcop⟩
    have hs := residualPool_supported G hG S ⟨I,hI⟩
    exact ⟨hI,(coprime_of_same_support Q Q' I hQ hQ' hs.1 hQQ').mpr hcop⟩

private theorem column_gauss (Q G : Id) (hG : G≠0) (S : Finset Id)
    (I : columns Q G hG S) (z : O) :
    gaussRow (element Q G hG S I) (element_supported Q G hG S I) z=
      primaryGaussRow I z := by
  rw [primaryGaussRow,dite_eq_left (column_supported Q G hG S I)]
  rfl

private theorem sum_two_subtypes (S T : Finset Id) (f : Id→Id→ℂ) :
    (∑I : S,∑J : T,f I J)=∑I∈S,∑J∈T,f I J := by
  calc
    _=∑I : S,∑J∈T,f I J := by
      apply Finset.sum_congr rfl
      intro I hI
      exact Finset.sum_coe_sort T (fun J=>f I J)
    _=_ := Finset.sum_coe_sort S (fun I=>∑J∈T,f I J)

/-- The same child matrix, written on ideals, makes the equal-support
reindexing transparent.  It does not enlarge either actual finite pool. -/
def plainPair (s : Source ι a b) (ha : 0<a) (Q C D seed L : Id)
    (hC : C≠0) (hD : D≠0) (τ₁ τ₂ : Character) (t₁ t₂ : ℝ)
    (F : Id) (z : O) (kernel : Id→Id→ℂ) : ℂ :=
  ∑I∈columns Q C hC (sourceColumns s),∑J∈columns C D hD (sourceColumns s),
    ((originalResidual s ha seed C L I*heightCoeff τ₁ t₁ I*
        selectedTwist F I*primaryGaussRow I z)*
      star (originalResidual s ha seed D L J*heightCoeff τ₂ t₂ J*
        selectedTwist F J*primaryGaussRow J (-z)))*kernel I J

theorem plainPair_reindex (s : Source ι a b) (ha : 0<a)
    (C D seed L : Id) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (τ₁ τ₂ : Character) (t₁ t₂ : ℝ)
    (F : Id) (z : O) (kernel : Id→Id→ℂ) :
    plainPair s ha C C D seed L hC hD τ₁ τ₂ t₁ t₂ F z kernel=
      plainPair s ha D C D seed L hC hD τ₁ τ₂ t₁ t₂ F z kernel := by
  unfold plainPair
  rw [columns_same_support C D C hC (sourceColumns s) hC hD hCD]

/-- The normalized positive weights are introduced exactly as square roots
on the two sides of Cauchy.  Their product is w(F)/W, including zero weights. -/
theorem rowVector_pair (s : Source ι a b) (ha : 0<a) (C D seed L : Id)
    (hC : C≠0) (hD : D≠0) (τ₁ τ₂ : Character) (t₁ t₂ : ℝ)
    (w : Id→ℝ) (W : ℝ) (hW : 0<W) (F : Id) (hw : 0≤w F)
    (z : O) (kernel : Id→Id→ℂ) :
    (∑I : Columns s D C hC,∑J : Columns s C D hD,
      (rowVector s ha D C seed L hC τ₁ t₁ w W false (F,z) I*
        star (rowVector s ha C D seed L hD τ₂ t₂ w W true (F,z) J))*kernel I J)=
      ((w F/W:ℝ):ℂ)*plainPair s ha D C D seed L hC hD τ₁ τ₂ t₁ t₂ F z kernel := by
  have hsqrt : (Real.sqrt (w F/W):ℂ)*(Real.sqrt (w F/W):ℂ)=((w F/W:ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←pow_two,Real.sq_sqrt (div_nonneg hw hW.le)]
  have hterm (I : Columns s D C hC) (J : Columns s C D hD) :
      (rowVector s ha D C seed L hC τ₁ t₁ w W false (F,z) I*
        star (rowVector s ha C D seed L hD τ₂ t₂ w W true (F,z) J))*kernel I J=
      ((w F/W:ℝ):ℂ)*
        ((originalResidual s ha seed C L I*heightCoeff τ₁ t₁ I*
          selectedTwist F I*primaryGaussRow I z)*
        star (originalResidual s ha seed D L J*heightCoeff τ₂ t₂ J*
          selectedTwist F J*primaryGaussRow J (-z)))*kernel I J := by
    simp only [rowVector,base,Bool.false_eq_true,if_false,if_true,selectedTwist,
      column_gauss,star_mul,Complex.star_def,Complex.conj_ofReal]
    calc
      _=((Real.sqrt (w F/W):ℂ)*(Real.sqrt (w F/W):ℂ))*
          ((originalResidual s ha seed C L I*heightCoeff τ₁ t₁ I*
            (idealRowHom (primaryGenerator F) I.val)^2*primaryGaussRow I z)*
          star (originalResidual s ha seed D L J*heightCoeff τ₂ t₂ J*
            (idealRowHom (primaryGenerator F) J.val)^2*primaryGaussRow J (-z)))*kernel I J := by
        simp only [star_mul,Complex.star_def,map_mul,map_pow]
        ring
      _=_ := by rw [hsqrt]; simp only [star_mul,Complex.star_def,map_mul,map_pow]
  simp_rw [hterm]
  let f : Id→Id→ℂ:=fun I J=>((w F/W:ℝ):ℂ)*
    ((originalResidual s ha seed C L I*heightCoeff τ₁ t₁ I*
      selectedTwist F I*primaryGaussRow I z)*
    star (originalResidual s ha seed D L J*heightCoeff τ₂ t₂ J*
      selectedTwist F J*primaryGaussRow J (-z)))*kernel I J
  have hs := sum_two_subtypes (columns D C hC (sourceColumns s))
    (columns C D hD (sourceColumns s)) f
  simpa only [f,plainPair,Finset.mul_sum,mul_assoc] using hs

def activeRow (C D : Id) (hC : Supported C) : O→ℂ :=
  finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)

def commonPhase (C D : Id) (hC : Supported C) (p : Id×O) : ℂ :=
  selectedTwist p.1 C*star (selectedTwist p.1 D)*star (activeRow C D hC p.2)

theorem commonPhase_norm (C D : Id) (hC : Supported C) (p : Id×O) :
    ‖commonPhase C D hC p‖≤1 := by
  have hr : ‖activeRow C D hC p.2‖≤1 :=
    QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _
  simp only [commonPhase,norm_mul,norm_star]
  exact (mul_le_mul (mul_le_mul (selectedTwist_norm p.1 C)
    (selectedTwist_norm p.1 D) (norm_nonneg _) zero_le_one)
    hr (norm_nonneg _) (by positivity)).trans_eq (by norm_num)

def artificialDivisors (s : Source ι a b) (C D : Id) (hD : D≠0) : Finset Id :=
  divisorPool (Finset.univ : Finset (columns C D hD (sourceColumns s)))
    (fun J=>Ideal.span {element C D hD (sourceColumns s) J})

def physicalKernel (Wprofile : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ)
    (C D : Id) (E : Finset (CommonIndex C D)) (K K₀ H₀ A₀ B₀ : ℝ)
    (z : O) (I J : Id) : ℂ :=
  let e:=primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E
  wholeKernel Wprofile V (K₀*H₀/(A₀*B₀))
    (Real.log (((K/‖eisEmbedding e‖^2)/‖eisEmbedding (activeConductor C D)‖^2)/K₀))
    (Real.log (‖eisEmbedding z‖^2/H₀))
    (Real.log ((I.absNorm:ℝ)/A₀)) (Real.log ((J.absNorm:ℝ)/B₀))

/-- A small, typed abbreviation for the baseline RHS.  In particular the
active character is passed as a function, rather than exposed through its
two definitionally equal presentations of the bad prime during rewriting. -/
private def rawChild (C D : Id) (hC : Supported C) (hD : Supported D)
    (S : Finset Id) (c d : Id→ℂ) (e r : O) (ρ : O→ℂ) (z : O)
    (Wprofile : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (Rwindow v x A₀ B₀ : ℝ) : ℂ :=
  ∑I : columns C C hC.1 S,∑J : columns C D hD.1 S,
    ((if IsCoprime (element C C hC.1 S I) (element C D hD.1 S J) then
        originalPhase e r ρ (element C C hC.1 S I) (element C D hD.1 S J) else 0)*
      (c I*star (d J)))*
    (gaussRow (element C C hC.1 S I) (element_supported C C hC.1 S I) z*
      star (gaussRow (element C D hD.1 S J) (element_supported C D hD.1 S J) (-z)))*
    wholeKernel Wprofile V Rwindow v x
      (Real.log (‖eisEmbedding (element C C hC.1 S I)‖^2/A₀))
      (Real.log (‖eisEmbedding (element C D hD.1 S J)‖^2/B₀))

/-- One actual physical block after exact Möbius/ray separation.  All
artificial divisors and FixedPairs are selected independently of F. -/
theorem block_selected_children (s : Source ι a b) (ha : 0<a)
    (seed F : Id) (η : Character) (t : ℝ) (C D : Id)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Wprofile : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0<K) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
        (selectedCoefficient s ha seed F) C D hC hD E rows Wprofile V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀*
        ∑z∈rows,commonPhase C D hC (F,z)*
          ∑L∈artificialDivisors s C D hD.1,
            (UniqueFactorizationMonoid.moebius L:ℂ)*
              activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)*
            ∑χ : RayCharacter,∑ξ : RayCharacter,
              pairCoeff firstPhaseTable χ ξ*
                plainPair s ha D C D seed L hC.1 hD.1
                  (fixedPair η C D hC E χ (ξ⁻¹)).left
                  (fixedPair η C D hC E χ (ξ⁻¹)).right t t F z
                  (physicalKernel Wprofile V C D E K K₀ H₀ A₀ B₀ z) := by
  have hwhole :
      block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
        (selectedCoefficient s ha seed F) C D hC hD E rows Wprofile V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀*∑z∈rows,star (activeRow C D hC z)*
        rawChild C D hC hD (sourceColumns s)
          (coefficient η (fixedBadMask*idealGenerator s.R) 1 t (selectedCoefficient s ha seed F) C)
          (coefficient η (fixedBadMask*idealGenerator s.R) 1 t (selectedCoefficient s ha seed F) D)
          (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)
          (activeConductor C D) (activeRow C D hC) z Wprofile V (K₀*H₀/(A₀*B₀))
          (Real.log (((K/‖eisEmbedding (primeSubsetGenerator
            (fun P : CommonIndex C D=>P.val) E)‖^2)/
            ‖eisEmbedding (activeConductor C D)‖^2)/K₀))
          (Real.log (‖eisEmbedding z‖^2/H₀)) A₀ B₀ :=
    block_eq_whole η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (selectedCoefficient s ha seed F) C D hC hD hCD E rows hrows
      Wprofile V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  rw [hwhole]
  refine congrArg (fun q : ℂ=>scalar C D hC E K A₀ B₀*q) ?_
  apply Finset.sum_congr rfl
  intro z hz
  unfold rawChild
  let e:=primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=activeRow C D hC
  let aL:=element C C hC.1 (sourceColumns s)
  let aR:=element C D hD.1 (sourceColumns s)
  let κ:=physicalKernel Wprofile V C D E K K₀ H₀ A₀ B₀ z
  have hnormL (I : Columns s C C hC.1) :
      ‖eisEmbedding (aL I)‖^2=(I.val.absNorm:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hnormR (J : Columns s C D hD.1) :
      ‖eisEmbedding (aR J)‖^2=(J.val.absNorm:ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  simp only [eisEmbedding_norm_sq_eq_absNorm_span,element_span]
  have hh := finite_first_children
    (Finset.univ : Finset (Columns s C C hC.1))
    (Finset.univ : Finset (Columns s C D hD.1)) aL aR
    (element_supported C C hC.1 (sourceColumns s))
    (element_supported C D hD.1 (sourceColumns s))
    (element_primary C C hC.1 (sourceColumns s))
    (element_primary C D hD.1 (sourceColumns s))
    (fun I=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t
      (selectedCoefficient s ha seed F) C I)
    (fun J=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t
      (selectedCoefficient s ha seed F) D J)
    e r ρ (finiteSexticRow_mul _ _ _) z (fun I J=>κ I J)
  simp only [κ,physicalKernel,eisEmbedding_norm_sq_eq_absNorm_span] at hh
  change star (ρ z)*_= _
  rw [hh]
  simp only [commonPhase,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ξ hξ
  let P:=fixedPair η C D hC E χ (ξ⁻¹)
  have hl (I : Columns s C C hC.1) :
      divisorCoefficient L aL
        (fun J=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t
          (selectedCoefficient s ha seed F) C J*leftCoefficient e r ρ (aL J)) χ I=
      selectedTwist F C*(originalResidual s ha seed C L I*heightCoeff P.left t I)*
        selectedTwist F I := by
    exact selected_divisor_column s ha seed F C L I
      (column_supported C C hC.1 (sourceColumns s) I) η P.left
      (leftCoefficient e r ρ) χ P.left_height t
  have hr (J : Columns s C D hD.1) :
      divisorCoefficient L aR
        (fun I=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t
          (selectedCoefficient s ha seed F) D I*rightCoefficient e r ρ (aR I)) (ξ⁻¹) J=
      selectedTwist F D*(originalResidual s ha seed D L J*heightCoeff P.right t J)*
        selectedTwist F J := by
    exact selected_divisor_column s ha seed F D L J
      (column_supported C D hD.1 (sourceColumns s) J) η P.right
      (rightCoefficient e r ρ) (ξ⁻¹) P.right_height t
  rw [←plainPair_reindex s ha C D seed L hC.1 hD.1 hCD P.left P.right t t F z κ]
  unfold plainPair
  rw [←sum_two_subtypes (columns C C hC.1 (sourceColumns s))
    (columns C D hD.1 (sourceColumns s))
    (fun I J=>((originalResidual s ha seed C L I*heightCoeff P.left t I*
      selectedTwist F I*primaryGaussRow I z)*
      star (originalResidual s ha seed D L J*heightCoeff P.right t J*
        selectedTwist F J*primaryGaussRow J (-z)))*κ I J)]
  simp only [hl,hr,column_gauss,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [aL,aR,column_gauss,κ,physicalKernel,eisEmbedding_norm_sq_eq_absNorm_span,ρ,e]
  ring

/-- The literal matrix appearing in IntegratedWindows.  No norm or absolute
value is taken before the common Fourier representation. -/
def weightedPair (s : Source ι a b) (ha : 0<a) (C D seed L : Id)
    (hC : C≠0) (hD : D≠0) (τ₁ τ₂ : Character) (t₁ t₂ : ℝ)
    (w : Id→ℝ) (W : ℝ) (p : Id×O) (kernel : Id→Id→ℂ) : ℂ :=
  ∑I : Columns s D C hC,∑J : Columns s C D hD,
    (rowVector s ha D C seed L hC τ₁ t₁ w W false p I*
      star (rowVector s ha C D seed L hD τ₂ t₂ w W true p J))*kernel I J

private theorem finite_average_reorder
    (Ds : Finset Id) (rows : Finset O) (Ls : Finset Id)
    (weight : Id→ℂ) (phase : Id×O→ℂ) (outer : Id→ℂ)
    (ray : RayCharacter→RayCharacter→ℂ)
    (value : Id→RayCharacter→RayCharacter→Id×O→ℂ) :
    (∑F∈Ds,weight F*∑z∈rows,phase (F,z)*∑L∈Ls,outer L*
      ∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*value L χ ξ (F,z))=
    ∑L∈Ls,outer L*∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*
      ∑p∈Ds×ˢrows,phase p*(weight p.1*value L χ ξ p) := by
  have hs : (∑F∈Ds,weight F*∑z∈rows,phase (F,z)*∑L∈Ls,outer L*
      ∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*value L χ ξ (F,z))=
      ∑p∈Ds×ˢrows,weight p.1*phase p*∑L∈Ls,outer L*
        ∑χ : RayCharacter,∑ξ : RayCharacter,ray χ ξ*value L χ ξ p := by
    simp only [Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hs]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact finite E1 endpoint.  The whole first common-height factor,
the physical scalar, Möbius projector and finite rays are retained.
The selected average is INSIDE the single common wholeKernel matrix.
For numerical application take s = avoidSource s0 u, V = logAnnulus;
IntegratedWindows supplies the bound for each displayed weightedPair.
Its two independent KL/KR row bounds are not collapsed in this identity. -/
theorem selected_physical_average (s : Source ι a b) (ha : 0<a)
    (seed : Id) (η : Character) (t : ℝ) (C D : Id)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (E : Finset (CommonIndex C D)) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (Ds : Finset Id) (weight : Id→ℝ) (W : ℝ) (hW : 0<W)
    (hw : ∀F∈Ds,0≤weight F)
    (Wprofile : 𝓢(ℝ,ℂ)) (V : Fin 4→ℝ→ℂ) (K K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0<K) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    commonHeight s η t C D*
      (∑F∈Ds,((weight F/W:ℝ):ℂ)*
        block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
          (selectedCoefficient s ha seed F) C D hC hD E rows Wprofile V K K₀ H₀ A₀ B₀)=
    commonHeight s η t C D*scalar C D hC E K A₀ B₀*
      ∑L∈artificialDivisors s C D hD.1,
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)*
        ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
          ∑p∈Ds×ˢrows,commonPhase C D hC p*
            weightedPair s ha C D seed L hC.1 hD.1
              (fixedPair η C D hC E χ (ξ⁻¹)).left
              (fixedPair η C D hC E χ (ξ⁻¹)).right t t weight W p
              (physicalKernel Wprofile V C D E K K₀ H₀ A₀ B₀ p.2) := by
  let e:=primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E
  let outer:=fun L : Id=>(UniqueFactorizationMonoid.moebius L:ℂ)*activeRow C D hC e
  let value:=fun (L : Id) (χ ξ : RayCharacter) (p : Id×O)=>
    plainPair s ha D C D seed L hC.1 hD.1
      (fixedPair η C D hC E χ (ξ⁻¹)).left
      (fixedPair η C D hC E χ (ξ⁻¹)).right t t p.1 p.2
      (physicalKernel Wprofile V C D E K K₀ H₀ A₀ B₀ p.2)
  have hb (F : Id) := block_selected_children s ha seed F η t C D hC hD hCD
    E rows hrows Wprofile V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  have hm (L : Id) (χ ξ : RayCharacter) (p : Id×O) (hp : p∈Ds×ˢrows) :
      weightedPair s ha C D seed L hC.1 hD.1
        (fixedPair η C D hC E χ (ξ⁻¹)).left
        (fixedPair η C D hC E χ (ξ⁻¹)).right t t weight W p
        (physicalKernel Wprofile V C D E K K₀ H₀ A₀ B₀ p.2)=
      ((weight p.1/W:ℝ):ℂ)*value L χ ξ p :=
    rowVector_pair s ha C D seed L hC.1 hD.1
      (fixedPair η C D hC E χ (ξ⁻¹)).left
      (fixedPair η C D hC E χ (ξ⁻¹)).right t t weight W hW p.1
      (hw p.1 (Finset.mem_product.mp hp).1) p.2 _
  have he := finite_average_reorder Ds rows (artificialDivisors s C D hD.1)
    (fun F=>((weight F/W:ℝ):ℂ)) (commonPhase C D hC) outer
    (pairCoeff firstPhaseTable) value
  calc
    _=commonHeight s η t C D*scalar C D hC E K A₀ B₀*
        (∑F∈Ds,((weight F/W:ℝ):ℂ)*∑z∈rows,commonPhase C D hC (F,z)*
          ∑L∈artificialDivisors s C D hD.1,outer L*
            ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              value L χ ξ (F,z)) := by
      rw [mul_assoc]
      congr 1
      simp_rw [hb]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      dsimp only [outer,value,e]
      ring
    _=commonHeight s η t C D*scalar C D hC E K A₀ B₀*
        (∑L∈artificialDivisors s C D hD.1,outer L*
          ∑χ : RayCharacter,∑ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑p∈Ds×ˢrows,commonPhase C D hC p*
              (((weight p.1/W:ℝ):ℂ)*value L χ ξ p)) := by rw [he]
    _=_ := by
      refine congrArg (fun q : ℂ=>commonHeight s η t C D*scalar C D hC E K A₀ B₀*q) ?_
      apply Finset.sum_congr rfl
      intro L hL
      refine congrArg (fun q : ℂ=>outer L*q) ?_
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro ξ hξ
      refine congrArg (fun q : ℂ=>pairCoeff firstPhaseTable χ ξ*q) ?_
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg (fun q : ℂ=>commonPhase C D hC p*q) (hm L χ ξ p hp).symm

end
end Candidate.FourthPower.MixedFirstPhysicalApplication
