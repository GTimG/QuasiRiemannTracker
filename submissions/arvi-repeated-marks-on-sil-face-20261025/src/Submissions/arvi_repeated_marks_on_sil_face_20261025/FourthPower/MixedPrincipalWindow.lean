/- Copyright (c) 2026 Sil. Apache-2.0.
Actual original-column Fourier windows in the inner exceptional branch.
The right source retains its inverse ray, conjugate window and -z.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedPrincipalAllocations
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.ReflectedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentLattice
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily
open CenteredMomentChildAssembly CenteredMomentSecondScaled
open CenteredMomentSecondMaskedWindow CenteredMomentSecondWindowSource
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic CenteredMomentReflectedSource
open CenteredMomentExceptionalWholeWindow CenteredMomentAllocatedNaturalRadial
open MixedPrincipalPair MixedPrincipalHeights MixedPrincipalAllocations
open MixedOriginalSource MixedHeightEnergy MixedLiveNormalization
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def sourceColumns (s : Source ι a b) : Finset Id :=
  finiteColumns (Fintype.piFinset (tuplePools s))

def sourceCoefficient (s : Source ι a b) (ha : 0<a) (seed : Id) : Id→ℂ :=
  originalColumn s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    b s.X₁ s.X₂ s.Y₁ s.Y₂

def sectorCoefficient (s : Source ι a b) (ha : 0<a) (G : Id) (hG : Supported G)
    (seed D : Id) (I : sectorPool G hG.1 (sourceColumns s)) : ℂ :=
  normalization (s.X₁*s.X₂) s.P*
    (if D∣I.val then sourceCoefficient s ha seed (G*I) else 0)

def heightRow (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (t : ℝ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
    (fun I=>sectorCoefficient s ha G hG seed D I*heightCoeff τ t I) z

def windowRow (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (t θ X : ℝ) (z : O) : ℂ :=
  rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
    (fun I=>sectorCoefficient s ha G hG seed D I*heightCoeff τ t I*
      columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z

/-- Literal divisor/moving/ray coefficient; the original normalization
is outside the row, exactly as in the physical dictionary. -/
def movingWindow (s : Source ι a b) (ha : 0<a) (η : Character) (χ : RayCharacter) (A : O)
    (G : Id) (hG : Supported G) (seed D : Id) (t θ X : ℝ) (z : O) : ℂ :=
  normalization (s.X₁*s.X₂) s.P*
    rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
      (fun I=>divisorCoefficient D (sectorElement G hG.1 (sourceColumns s))
        (movingCoefficient A (sectorElement G hG.1 (sourceColumns s))
          (fun J=>sourceCoefficient s ha seed (G*J)*heightCoeff η t J)) χ I*
        columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) z

def conjugateWindow (s : Source ι a b) (ha : 0<a) (η : Character) (χ : RayCharacter) (A : O)
    (G : Id) (hG : Supported G) (seed D : Id) (t θ X : ℝ) (z : O) : ℂ :=
  normalization (s.X₁*s.X₂) s.P*
    rowPolynomial Finset.univ (sectorElement G hG.1 (sourceColumns s))
      (fun I=>divisorCoefficient D (sectorElement G hG.1 (sourceColumns s))
        (movingCoefficient A (sectorElement G hG.1 (sourceColumns s))
          (fun J=>sourceCoefficient s ha seed (G*J)*heightCoeff η t J)) χ I*
        star (columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ)) z

theorem height_row_norm (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (v : ℝ) (z : O) (hz : z≠0) :
    ‖heightRow s ha τ G hG seed D v z‖=
      ‖originalRow s ha (naturalCharacter τ z) G hG.1 seed D v‖ := by
  unfold heightRow sectorCoefficient
  simp only [mul_assoc,rowPolynomial_factor]
  exact original_sector_norm s ha τ G hG seed D v z hz

/-- Exact reflection of the height row; no new reflected conductor
bound is needed when the original right row is controlled at -z. -/
theorem height_row_neg (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (t : ℝ) (z : O) :
    heightRow s ha τ G hG seed D t (-z)=
      heightRow s ha (reflected τ) G hG seed D t z := by
  simpa only [heightRow,sectorElement_span] using polynomial_neg Finset.univ
    (sectorElement G hG.1 (sourceColumns s))
    (sectorElement_supported G hG.1 (sourceColumns s))
    (sectorCoefficient s ha G hG seed D) τ t z

theorem window_row_neg (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (t θ X : ℝ) (z : O) :
    windowRow s ha τ G hG seed D t θ X (-z)=
      windowRow s ha (reflected τ) G hG seed D t θ X z := by
  have he := polynomial_neg Finset.univ (sectorElement G hG.1 (sourceColumns s))
    (sectorElement_supported G hG.1 (sourceColumns s))
    (fun I=>sectorCoefficient s ha G hG seed D I*
      columnPhase logAnnulus (Real.log ((I.val.absNorm:ℝ)/X)) θ) τ t z
  simpa only [windowRow,sectorElement_span,mul_right_comm] using he

theorem moving_window_eq (s : Source ι a b) (ha : 0<a) (η τ : Character)
    (χ : RayCharacter) (A : O) (G : Id) (hG : Supported G)
    (hτ : ∀I : Id,Supported I→IsCoprime G I→∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (seed D : Id) (t θ X : ℝ) (z : O) :
    movingWindow s ha η χ A G hG seed D t θ X z=
      windowRow s ha τ G hG seed D t θ X z := by
  unfold movingWindow
  simp_rw [masked_divisor_coefficient η τ χ A G hG hτ]
  simp only [windowRow,sectorCoefficient,mul_assoc,rowPolynomial_factor]

theorem conjugate_window_eq (s : Source ι a b) (ha : 0<a) (η τ : Character)
    (χ : RayCharacter) (A : O) (G : Id) (hG : Supported G)
    (hτ : ∀I : Id,Supported I→IsCoprime G I→∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (seed D : Id) (t θ X : ℝ) (z : O) :
    conjugateWindow s ha η χ A G hG seed D t θ X z=
      windowRow s ha τ G hG seed D t (-θ) X z := by
  change conjugateWindow s ha η χ A G hG seed D t θ X z=_
  simpa only [conjugateWindow,movingWindow,star_logAnnulus_column] using
    moving_window_eq s ha η τ χ A G hG hτ seed D t (-θ) X z

def windowMoment (J : ℕ) : ℝ :=
  ∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖

theorem pair_budget_nonneg (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G₁ G₂ : Id) (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε α : ℝ) (hZ : 0≤Z) :
    0≤pairBudget s hb cover G₁ G₂ J control Z ε α := by
  unfold pairBudget
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (mul_nonneg ((allocationSource s hb cover G₁ p.1).budget_nonneg J control Z ε hZ)
      ((allocationSource s hb cover G₂ p.2).budget_nonneg J control Z ε hZ))
    (le_min ((allocationSource s hb cover G₁ p.1).saving_nonneg α)
      ((allocationSource s hb cover G₂ p.2).saving_nonneg α))

/-- Actual whole original-source window pair. The right factor uses
the inverse ray, the conjugate window and -z exactly. The only displayed
cost not yet summed is the actual genuine-allocation budget. -/
theorem uniform_original_window_pair (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,
      ∀cover : OriginalEnclosure s,∀Z : ℝ,1≤Z→Fintype.card ι≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→
      ∀G₁ G₂ : Id,∀hG₁ : Supported G₁,∀hG₂ : Supported G₂,
      ∀seed : Id,seed∣G₁→seed∣G₂→
      ∀(η τ₁ τ₂ : Character)(χ ξ : RayCharacter)(A : O),
      (∀I : Id,Supported I→IsCoprime G₁ I→∀v : ℝ,
        heightCoeff τ₁ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))→
      (∀I : Id,Supported I→IsCoprime G₂ I→∀v : ℝ,
        heightCoeff τ₂ v I=heightCoeff η v I*idealRowHom A I*rayCharacter (ξ⁻¹) (primaryGenerator I))→
      ∀(t θ X Y : ℝ),0<X→0<Y→
      ∀(rows : Finset O)(Ds : Finset Id)(μ : Id→ℂ),
      (∀z∈rows,z≠0)→(∀D∈Ds,Squarefree D)→(∀D∈Ds,‖μ D‖≤1)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound τ₁
        (fixedBadMask*idealGenerator ((s.R*G₁)*D)) 1 z:ℝ)≤Z^Bcap)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound τ₂
        (fixedBadMask*idealGenerator ((s.R*G₂)*D)) 1 (-z):ℝ)≤Z^Bcap)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z))→
      (∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖movingWindow s ha η χ A G₁ hG₁ seed D t θ X z‖*
        ‖conjugateWindow s ha η (ξ⁻¹) A G₂ hG₂ seed D t θ Y (-z)‖)≤
      (rows.card:ℝ)*C*pairBudget s hb cover G₁ G₂ J control Z ε α*
        heightCost t θ^J*heightCost t (-θ)^J*(windowMoment J)^2 := by
  obtain ⟨J,control,h00,hsource⟩ := uniform_original_height_pair N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hsource⟩ := hsource Q hQ
  refine ⟨C,hC,?_⟩
  intro ι instι s cover Z hZ hι hF hP G₁ G₂ hG₁ hG₂ seed hs₁ hs₂
    η τ₁ τ₂ χ ξ A hτ₁ hτ₂ t θ X Y hX hY rows Ds μ hrows hDs hμ hc₁ hc₂ he₁ he₂
  let c := sectorCoefficient s ha G₁ hG₁ seed
  let d := sectorCoefficient s ha G₂ hG₂ seed
  let B := (rows.card:ℝ)*C*pairBudget s hb cover G₁ G₂ J control Z ε α
  let E := B*heightCost t θ^J*heightCost t (-θ)^J
  have hB : 0≤B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC.le)
    (pair_budget_nonneg s hb cover G₁ G₂ J control Z ε α (zero_le_one.trans hZ))
  have hE : 0≤E := mul_nonneg
    (mul_nonneg hB (pow_nonneg (heightCost_pos t θ).le _))
    (pow_nonneg (heightCost_pos t (-θ)).le _)
  have hpair (u v : ℝ) :
      (∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖heightRow s ha τ₁ G₁ hG₁ seed D (t+2*Real.pi*(u-θ)) z‖*
        ‖heightRow s ha (reflected τ₂) G₂ hG₂ seed D (t+2*Real.pi*(v-(-θ))) z‖)≤
        E*(1+‖u‖)^J*(1+‖v‖)^J := by
    have hp := hsource ι s cover Z hZ hι hF hP G₁ G₂ hG₁.1 hG₂.1 seed hs₁ hs₂
      (t+2*Real.pi*(u-θ)) (t+2*Real.pi*(v-(-θ))) τ₁ τ₂ rows Ds μ
      hrows hDs hμ hc₁ hc₂ he₁ he₂
    have heq :
        (∑D∈Ds,‖μ D‖*∑z∈rows,
          ‖heightRow s ha τ₁ G₁ hG₁ seed D (t+2*Real.pi*(u-θ)) z‖*
          ‖heightRow s ha (reflected τ₂) G₂ hG₂ seed D (t+2*Real.pi*(v-(-θ))) z‖)=
        ∑D∈Ds,‖μ D‖*∑z∈rows,
          ‖originalRow s ha (naturalCharacter τ₁ z) G₁ hG₁.1 seed D (t+2*Real.pi*(u-θ))‖*
          ‖originalRow s ha (naturalCharacter τ₂ (-z)) G₂ hG₂.1 seed D (t+2*Real.pi*(v-(-θ)))‖ := by
      apply Finset.sum_congr rfl
      intro D hD
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [←height_row_neg,height_row_norm s ha τ₁ G₁ hG₁ seed D _ z (hrows z hz),
        height_row_norm s ha τ₂ G₂ hG₂ seed D _ (-z) (neg_ne_zero.mpr (hrows z hz))]
    rw [heq]
    apply hp.trans
    have h₁ := pow_le_pow_left₀ (by positivity : 0≤1+‖t+2*Real.pi*(u-θ)‖)
      (norm_height_shift t θ u) J
    have h₂ := pow_le_pow_left₀ (by positivity : 0≤1+‖t+2*Real.pi*(v-(-θ))‖)
      (norm_height_shift t (-θ) v) J
    have hprod := mul_le_mul h₁ h₂ (by positivity)
      (pow_nonneg (mul_nonneg (heightCost_pos t θ).le (by positivity)) _)
    have hh := mul_le_mul_of_nonneg_left hprod hB
    simpa only [mul_pow,E,B,mul_assoc,mul_left_comm,mul_comm] using hh
  have hw := whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sectorElement G₁ hG₁.1 (sourceColumns s)) (sectorElement G₂ hG₂.1 (sourceColumns s))
    (sectorElement_supported G₁ hG₁.1 (sourceColumns s))
    (sectorElement_supported G₂ hG₂.1 (sourceColumns s)) c d τ₁ (reflected τ₂)
    t t θ (-θ) X Y hX hY logAnnulus logAnnulus logAnnulus_compact logAnnulus_compact
    logAnnulus_smooth logAnnulus_smooth J J E hE (by
      intro u v
      simpa only [heightRow,c,d,sectorElement_span] using hpair u v)
  have hw' :
      (∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖windowRow s ha τ₁ G₁ hG₁ seed D t θ X z‖*
        ‖windowRow s ha τ₂ G₂ hG₂ seed D t (-θ) Y (-z)‖)≤
      E*(windowMoment J)*(windowMoment J) := by
    have hw₀ :
        (∑D∈Ds,‖μ D‖*∑z∈rows,
          ‖windowRow s ha τ₁ G₁ hG₁ seed D t θ X z‖*
          ‖windowRow s ha (reflected τ₂) G₂ hG₂ seed D t (-θ) Y z‖)≤
        E*(windowMoment J)*(windowMoment J) := by
      simpa only [windowRow,c,d,sectorElement_span,windowMoment] using hw
    simpa only [window_row_neg] using hw₀
  calc
    _ = ∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖windowRow s ha τ₁ G₁ hG₁ seed D t θ X z‖*
        ‖windowRow s ha τ₂ G₂ hG₂ seed D t (-θ) Y (-z)‖ := by
      simp_rw [moving_window_eq s ha η τ₁ χ A G₁ hG₁ hτ₁,
        conjugate_window_eq s ha η τ₂ (ξ⁻¹) A G₂ hG₂ hτ₂]
    _ ≤ E*(windowMoment J)*(windowMoment J) := hw'
    _ = _ := by dsimp only [E,B];ring

end
end Candidate.FourthPower.MixedPrincipalWindow
