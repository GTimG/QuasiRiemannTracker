import Candidate.Cycle63.Marked.ActualMarkedPlainProfiles
import Candidate.Cycle63.Marked.NaturalSlotHeight

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63MarkedPlain
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
local instance actualRowwiseMarkedPlainFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual marked plain moments with a row-dependent common slot frequency.
The additional parameter costs one polynomial power of the height bound. -/
theorem actual_rowwise_marked_plain_energy_fixedmesh
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
      ∀χ : Row→ Character,
      (∀u∈rows,∀n,elementCoeff (χ u) n=
        CanonicalRowCompletion.rowTwist (elementHom η)
          (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
          1 (1*row u) n) →
      (∀u∈rows,initialKeep η (internalQ Q η₀) (row u)) →
      (∀u∈rows,‖eisEmbedding (row u)‖^2≤U) →
      ∀(m : ℝ),0≤ m → m≤1 →
      ∀(slots : Finset α)(θ : slots→RayQuotient.Characters M H)(w σ v : slots→ℝ)
        (height : ℝ)(choice : Row→ℝ),
      (∀s,0≤w s) → (∀s,w s≤ markedPlainMesh κ εm) →
      (∀s,lo≤σ s) → (∀s,σ s≤hi) → 0≤height → (∀s,|v s|≤height) →
      (∀u∈rows,|choice u|≤height) →
      2*m+6*κ*(∑s,w s)≤1 →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
          (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (choice u+v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  let N := Fintype.card α
  obtain ⟨J,C,hC,hfield⟩ := actual_common_profiles_marked_plain_energy_fixedmesh (α:=α)
    M H hH W aslot bslot bΦ lo hi κ εm haslot hWs hW hbslot hbΦ hrad hκ hεm hβ hκβ
    η η₀ Q hQM hQ0 hQt hQ72 N
  let K := Cycle63MarkedHeight.commonProfileCost N
  have hK : 0<K := zero_lt_one.trans_le (Cycle63MarkedHeight.commonProfileCost_ge_one N)
  refine ⟨J+1,4*K*C*2^J,by positivity,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height choice
    hw hwm hσlo hσhi hheight hv hchoice hcap j k hjk σd hσd td htd
  have hUp : 0<U := zero_lt_one.trans hU.1
  let factor := fun u=>polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
    polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td
  let E := C*(1+2*height)^J*U^(1+εm)
  have hE : 0≤E := by dsimp [E];positivity
  have hcard : (Finset.univ : Finset slots).card≤N := by
    simpa only [Finset.card_univ,Fintype.card_coe] using Finset.card_le_univ slots
  have hmoment (node : Fin (N+1)) (t : ℝ)(ht : t∈Icc (-height) height) :
      (∑u∈rows,‖factor u*(∏s : slots,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
        (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
          HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val)
            (U^(w s)) (σ s) (t+v s) I) (U^(w s)))‖^2)≤E := by
    apply (hU.2 node) rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ
      (fun s=>t+v s) (2*height) hw hwm hσlo hσhi (by positivity)
    · intro s
      exact (abs_add_le t (v s)).trans (by linarith [abs_le.mpr ht,hv s])
    · exact hcap
    · exact hjk
    · exact hσd
    · linarith
  have he := Cycle63MarkedHeight.naturalSlot_rowwise_energy rows (Finset.univ : Finset slots)
    N hcard χ (fun s=>CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
    (fun s _ I hI=>(Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun s I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I) W
    (fun s=>U^(w s)) σ v
    (fun s _=>Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) factor
    (-height) height E (by linarith) hE choice
    (fun u hu=>abs_le.mp (hchoice u hu)) hmoment
  apply he.trans
  have hheight' : 1+2*(height- -height)≤4*(1+height) := by linarith
  have hpow : (1+2*height)^J≤2^J*(1+height)^J := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  change (1+2*(height- -height))*K*(C*(1+2*height)^J*U^(1+εm))≤_
  calc
    _≤(4*(1+height))*K*(C*(2^J*(1+height)^J)*U^(1+εm)) := by
      gcongr
    _=_ := by rw [pow_succ];ring

end
end OAI.SevenEighths.Cycle63MarkedPlain
