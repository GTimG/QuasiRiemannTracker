/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalSource
import Candidate.Cycle63.Physical.InitialMass.GeometryLowAdmission
import Candidate.Cycle63.Physical.InitialMass.SecondDatumReindex

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153CanonicalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open ActualEisensteinCubic ConcretePrimeRowBridge LocalMoment
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonPairedSource CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearNormalization CenteredMomentEnergyBands
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyState
open CenteredMomentSourceInputReindex
open CenteredMomentNaturalFixedRaySource
open Cycle63Moment Cycle63Moment.LowBranch Cycle63FinalLow Cycle63FinalNatural
open Cycle63InitialMass Cycle153RegionalLow Cycle153LowPhysical
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Literal source metadata connecting the actual common chain with its
ordinary canonical block. These are field equalities, not energy or
capacity bounds. The unchanged native geometry constructor supplies them. -/
structure CanonicalSourceFrame (s : Input α) (ch : Chain s)
    {Z Mrow amp omega xi b : ℝ} {N : ℕ}
    (g : LiveMainGeometry s ch Z Mrow amp omega xi b N)
    (datum : SecondInputDatum α) (second : Bool) where
  slots : (CenteredMomentCommonProfile.liveIndices ch.B₁.val) ≃ datum.slots
  first_eq : reindex slots ch.first=datum.input
  datum_eq : g.datum=datum
  puncture_eq : ch.R₂=datum.R
  own_eq : ch.E₂=(if second then datum.D else datum.C)

variable {s : Input α} {ch : Chain s}
  {Z Mrow amp omega xi b : ℝ} {N : ℕ}
  {g : LiveMainGeometry s ch Z Mrow amp omega xi b N}
  {datum : SecondInputDatum α} {second : Bool}

/-- Canonical LOW row admission transported to the actual live state.
The source input, puncture and own ideal are the SAME literal fields. -/
theorem actual_chain_canonical_payment_gates
    (frame : CanonicalSourceFrame s ch g datum second)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) [Cycle63.AffineLedger]
    (χ₀ χ ψ : RayFourExpansion.RayCharacter) (Q : Ideal O)
    (hQ : Q ≤ Ideal.span {(72:O)}) (m : O) (hm : m≠0)
    (hml : goodLambda∣m) (hm₂ : (2:O)∣m) (Bmask : ℝ) (hZ : 1<Z)
    (hP : ch.R₂*ch.E₂≠0) (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ Z^Bmask)
    (η₀ : Character) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8) :
    let hp : datum.R*(if second then datum.D else datum.C)≠0 := by
      simpa only [frame.puncture_eq,frame.own_eq] using hP
    let hn : ((datum.R*(if second then datum.D else datum.C)).absNorm:ℝ)≤Z^Bmask := by
      simpa only [frame.puncture_eq,frame.own_eq] using hPN
    let ray := if second then ψ⁻¹ else χ
    let st := retainedState Z Bmask hZ (g.datum.τ ray) Q (ch.R₂*ch.E₂) hP hPN
      g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let rows := mainLowSourceRows second (ordinarySecondDatum datum χ₀ Q m) (fun _=>True)
    let select := mainLowCanonicalSelector M H hH datum χ₀ χ ψ Q hQ m hm hml hm₂ Z Bmask hZ second
      hp hn η₀ hQM hQη e T he hT hβlo hβhi
    ∀p z,z∈mainLowPaymentRows rows select p →
      st.radial.keep z ∧
      ActualLow M H hH st η₀ hQM hQη ((1+Cycle63.AffineLedger.q)/2) e (3*(p.1.val+1:ℕ)*T) z ∧
      1 ≤ (st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)).re ∧
      1 ≤ p.1.val ∧ p.1.val ≤ bufferCount e := by
  intro hp hn ray st rows select p z hz
  have hcanonical := actual_main_low_canonical_payment_bins M H hH datum χ₀ χ ψ Q hQ m hm hml hm₂
    Z Bmask hZ second hp hn η₀ hQM hQη e T he hT hβlo hβhi
  have hstate : st=retainedState Z Bmask hZ
      (if second then datum.τ ψ⁻¹ else datum.τ χ) Q
      (datum.R*(if second then datum.D else datum.C)) hp hn
      datum.radius datum.C datum.D datum.inactive := by
    have hd := frame.datum_eq
    subst datum
    dsimp only [st,ray]
    simp only [frame.puncture_eq,frame.own_eq]
    cases second <;> rfl
  simpa only [hstate,normValue_eq_embedding] using hcanonical p z hz

/-- Exact ordinary-to-actual normalized-column transport. The reciprocal
coefficient, original projector seed, source ray and signed height are
unmodified; this identity can be used inside the residual shell sum. -/
theorem actual_ordinary_column_eq_chain
    (frame : CanonicalSourceFrame s ch g datum second)
    (hE : Supported ch.E₂)
    (χ₀ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m : O)
    (ray : RayFourExpansion.RayCharacter) (heightV : ℝ) (D : Ideal O) (z : O) :
    normalizedColumn
      (withHeight (ordinarySecondDatum datum χ₀ Q m).input
        ((ordinarySecondDatum datum χ₀ Q m).τ ray) heightV)
      (if second then (ordinarySecondDatum datum χ₀ Q m).D else (ordinarySecondDatum datum χ₀ Q m).C)
      (mainLowPhysicalSupported second (ordinarySecondDatum datum χ₀ Q m))
      (ordinarySecondDatum datum χ₀ Q m).R (ordinarySecondDatum datum χ₀ Q m).seed D z =
    normalizedColumn (withHeight ch.first (g.datum.τ ray) heightV)
      ch.E₂ hE ch.R₂ datum.seed D z := by
  have hcanonical : normalizedColumn
      (withHeight datum.input (datum.τ ray) heightV)
      (if second then datum.D else datum.C) (mainLowPhysicalSupported second datum)
      datum.R datum.seed D z =
    normalizedColumn (withHeight ch.first (datum.τ ray) heightV)
      (if second then datum.D else datum.C) (mainLowPhysicalSupported second datum)
      datum.R datum.seed D z := by
    rw [←frame.first_eq]
    exact normalized_column_reindex_height frame.slots ch.first _ _ _ _ _ _ _ _
  have ht : normalizedColumn (withHeight ch.first (g.datum.τ ray) heightV)
      ch.E₂ hE ch.R₂ datum.seed D z =
    normalizedColumn (withHeight ch.first (datum.τ ray) heightV)
      (if second then datum.D else datum.C) (mainLowPhysicalSupported second datum)
      datum.R datum.seed D z := by
    simp only [frame.datum_eq,frame.puncture_eq,frame.own_eq]
  exact hcanonical.trans ht.symm
end
end OAI.SevenEighths.Cycle153CanonicalLow
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.actual_chain_canonical_payment_gates
#print axioms OAI.SevenEighths.Cycle153CanonicalLow.actual_ordinary_column_eq_chain
