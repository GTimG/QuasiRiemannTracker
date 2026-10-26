import Candidate.Cycle63.Marked.ActualMarkedPlain

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
local instance actualMarkedPlainProfilesFinite : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The finite common-profile family needed by the height interpolation
shares a single mesh, threshold, degree and constant. -/
theorem actual_common_profiles_marked_plain_energy_fixedmesh
    (W : ℝ→ℂ) (aslot bslot bΦ lo hi κ εm : ℝ)
    (haslot : 0<aslot) (hWs : Function.support W⊆Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0≤bslot) (hbΦ : 0<bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hκ : (3/4:ℝ)≤κ) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤κ)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (N : ℕ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧ ∀node : Fin (N+1),
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
        (height : ℝ),
      (∀s,0≤w s) → (∀s,w s≤ markedPlainMesh κ εm) →
      (∀s,lo≤σ s) → (∀s,σ s≤hi) → 0≤height → (∀s,|v s|≤height) →
      2*m+6*κ*(∑s,w s)≤1 →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
          (CenteredMomentPrimeSlot.primePool M H bslot (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight (Cycle63MarkedHeight.commonProfile W node.val) (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  have hnode (node : Fin (N+1)) := actual_marked_plain_energy_fixedmesh (α:=α) M H hH
    (Cycle63MarkedHeight.commonProfile W node.val) aslot bslot bΦ lo hi κ εm haslot
    ((Cycle63MarkedHeight.commonProfile_support W node.val).trans hWs)
    (Cycle63MarkedHeight.commonProfile_smooth W aslot bslot haslot hWs hW node.val)
    hbslot hbΦ hrad hκ hεm hβ hκβ η η₀ Q hQM hQ0 hQt hQ72
  choose J C hC hb using hnode
  have hne : (Finset.univ : Finset (Fin (N+1))).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hC₀ : 0<∑node,C node := Finset.sum_pos (fun node _=>hC node) hne
  refine ⟨∑node,J node,∑node,C node,hC₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb] with U hU
  refine ⟨(hU ⟨0,by omega⟩).1,?_⟩
  intro node Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hcap j k hjk σd hσd td htd
  have he := (hU node).2 rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm
    hσlo hσhi hheight hv hcap j k hjk σd hσd td htd
  have hc : C node≤∑node,C node := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
  have hj : J node≤∑node,J node := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ node)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans (hU node).1).le _)
  exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hj) (by positivity) hC₀.le

end
end OAI.SevenEighths.Cycle63MarkedPlain
