import Candidate.Cycle62.Marked.PositiveInput
import Candidate.Cycle62.Marked.NaturalMarkedPlainField

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily HeckeDyadic HeckeRowClosure
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainProfileControl
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The plain marked mesh depends only on scalar capacity and error parameters. -/
def markedPlainMesh (κ εm : ℝ) : ℝ := fineMesh 2 0 1 κ (min (εm/4) (1/4))

theorem markedPlainMesh_pos {κ εm : ℝ} (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm) :
    0<markedPlainMesh κ εm :=
  fineMesh_pos _ _ _ _ _ (by norm_num) (by norm_num) (by linarith)
    (lt_min (by positivity) (by norm_num))

/-- The actual marked plain detector estimate. No marked energy hypothesis is
assumed: the uniform analytic field comes from the incumbent terminal theorem.
Only literal row, scale, frequency and nonexceptional gates remain. -/
theorem actual_marked_plain_energy_fixedmesh
    (W : ℝ→ℂ) (aslot bslot bΦ lo hi κ εm : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hbΦ : 0<bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤κ)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom η)
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep η (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2≤U) →
      ∀(m : ℝ),0≤m → m≤1 →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)
        (height : ℝ),
      (∀s,0≤w s) → (∀s,w s≤markedPlainMesh κ εm) →
      (∀s,lo≤σ s) → (∀s,σ s≤hi) → 0≤height → (∀s,|v s|≤height) →
      2*m+6*κ*(∑s,w s)≤1 →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
          (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  let δ : ℝ := min (εm/4) (1/4)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδmax : δ≤1 := (min_le_right _ _).trans (by norm_num)
  have hδbudget : δ+δ≤εm := by
    have he : δ≤εm/4 := min_le_left _ _
    linarith
  obtain ⟨degree,seminorms,hinput⟩ := fixed_positive_input (α:=α) M H hH W aslot bslot
    (1/4) (9/4) bΦ 0 1 lo hi 2 κ δ haslot hWs hW hbslot
    (by norm_num) le_rfl (by norm_num) hbΦ (by norm_num) (by norm_num) hκ hδ hβ hκβ
  obtain ⟨A,hA,hinput⟩ := hinput η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨J,Cp,hCp,hprofiles⟩ := paired_control seminorms
  let C : ℝ := A*(1+diagonalControl radialMajorant)*Cp
  have hdiag : 0≤diagonalControl radialMajorant := diagonalControl_nonneg _
  have hC : 0<C := mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A*diagonalControl radialMajorant*Cp≤C := by
    dsimp [C]
    gcongr
    linarith
  refine ⟨J+degree,C,hC,?_⟩
  have hmod : ∀ᶠU : ℝ in atTop,(η.modulus.absNorm:ℝ)≤U^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  filter_upwards [hinput,hmod] with U hU hmU
  refine ⟨hU.1,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hcap j k hjk σd hσd td htd
  have he := finite_marked_plain_field M H hH W bslot bΦ
    (fineMesh 2 0 1 κ δ) lo hi δ κ U δ m η η₀ Q degree J seminorms A Cp hU.2
    (hprofiles false) hA.le hCp.le hU.1 hδ.le hδmax hmU hrad hm hmmax
    slots θ w σ v height hw hwm hσlo hσhi hheight hv hcap
    rows row hinj χ hrow hkeep hnorm j k hjk σd td hσd htd
  apply he.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hC' (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le hU.1.le (by linarith)
  · exact Real.rpow_nonneg (zero_lt_one.trans hU.1).le _
  · exact mul_nonneg hC.le (by positivity)


theorem actual_marked_plain_energy
    (W : ℝ→ℂ) (aslot bslot bΦ lo hi κ εm : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hbΦ : 0<bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤κ)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    ∃ mesh : ℝ,0<mesh ∧ ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀{Row : Type*}(rows : Finset Row)(row : Row→O),Function.Injective row →
      ∀χ : Row→Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom η)
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep η (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2≤U) →
      ∀(m : ℝ),0≤m → m≤1 →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)
        (height : ℝ),
      (∀s,0≤w s) → (∀s,w s≤mesh) →
      (∀s,lo≤σ s) → (∀s,σ s≤hi) → 0≤height → (∀s,|v s|≤height) →
      2*m+6*κ*(∑s,w s)≤1 →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
          (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  obtain ⟨J,C,hC,hfield⟩ := actual_marked_plain_energy_fixedmesh (α:=α) M H hH W aslot bslot bΦ lo hi κ εm haslot hWs hW hbslot hbΦ hrad hκ hεm hβ hκβ
    η η₀ Q hQM hQ0 hQt hQ72
  exact ⟨markedPlainMesh κ εm,markedPlainMesh_pos hκ hεm,J,C,hC,hfield⟩

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.actual_marked_plain_energy

#print axioms OAI.SevenEighths.Cycle62MarkedPlain.actual_marked_plain_energy_fixedmesh
