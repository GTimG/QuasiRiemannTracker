/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.UniformPlain
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Upstream.ActualMarkedPlainProfiles
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source
open Set Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentPositiveSummability CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentHeckeTwist CenteredMomentDetectorDictionary
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorPlainProfileControl
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ConcreteTraceCRT QuadraticInitialBound Cycle61MarkedPlain
local notation "O" => HeckeFamily.O
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ordinary_common_profiles_fixedmesh
    (B lam h mesh εm : ℝ) (hlam : 0≤lam)
    (hsource : QRH.Record12518109Existence.UnitFaceSource ⟨B,lam,0,B,0,h⟩ mesh εm)
    (W : ℝ→ℂ) (bΦ : ℝ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (hbΦ : 2≤bΦ)
    (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (η η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ0 : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (N : ℕ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧ ∀node : Fin (N+1),
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
      (∀s,(33/50:ℝ)≤σ s) → (∀s,σ s≤(33/50:ℝ)) → 0≤height → (∀s,|v s|≤height) →
      (∑s,w s)≤h → 2*m+lam*(∑s,w s)≤B →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀td : ℝ,|td|≤height →
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd td*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd td*
        ∏s,CenteredMomentCommonMaskExpansion.naturalSlot (χ u)
          (CenteredMomentPrimeSlot.primePool M H 2 (U^(w s)))
          (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
            HeckePrimeAnnular.annularWeight (Cycle61MarkedHeight.commonProfile W node.val) (U^(w s)) (σ s) (v s) I)
          (U^(w s))‖^2)≤C*(1+height)^J*U^(1+εm) := by
  have hnode (node : Fin (N+1)) := ordinary_plain_fixedmesh (α:=α) M H hH B lam h mesh εm hlam hsource
    (Cycle61MarkedHeight.commonProfile W node.val) bΦ
    ((Cycle61MarkedHeight.commonProfile_support W node.val).trans hWs)
    (Cycle61MarkedHeight.commonProfile_smooth W 1 2 (by norm_num) hWs hW node.val)
    hbΦ hrad η η₀ Q hQM hQ0 hQt hQ72
  choose J C hC hb using hnode
  have hne : (Finset.univ : Finset (Fin (N+1))).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  have hC₀ : 0<∑node,C node := Finset.sum_pos (fun node _=>hC node) hne
  refine ⟨∑node,J node,∑node,C node,hC₀,?_⟩
  filter_upwards [Filter.eventually_all.mpr hb] with U hU
  refine ⟨(hU ⟨0,by omega⟩).1,?_⟩
  intro node Row rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm hσlo hσhi hheight hv hwidth hcap j k hjk σd hσd td htd
  have he := (hU node).2 rows row hinj χ hrow hkeep hnorm m hm hmmax slots θ w σ v height
    hw hwm
    hσlo hσhi hheight hv hwidth hcap j k hjk σd hσd td htd
  have hc : C node≤∑node,C node := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ node)
  have hj : J node≤∑node,J node := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ node)
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_lt_one.trans (hU node).1).le _)
  exact mul_le_mul hc (pow_le_pow_right₀ (by linarith) hj) (by positivity) hC₀.le

end
end QRH.Record1252270103Source.High
#print axioms QRH.Record1252270103Source.High.ordinary_common_profiles_fixedmesh
