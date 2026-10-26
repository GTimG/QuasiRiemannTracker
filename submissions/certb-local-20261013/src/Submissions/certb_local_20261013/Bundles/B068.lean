/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.certb_local_20261013.Bundles.B033
import Submissions.certb_local_20261013.Bundles.B037
import Submissions.certb_local_20261013.Bundles.B046
import Submissions.certb_local_20261013.Bundles.B059
import Submissions.certb_local_20261013.Bundles.B060
import Submissions.certb_local_20261013.Bundles.B061
import Submissions.certb_local_20261013.Bundles.B063
import Submissions.certb_local_20261013.Bundles.B065
import Submissions.certb_local_20261013.Bundles.B066
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CappedRadialTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransport
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry

/- BEGIN ORIGINAL MODULE Analytic.JointSourceBuffered ; sha256 c75444b95ab948191f45b2ea9c0ad8dc674166a95aa1c22fb5a8ece91403c0be -/
section





/-! Construct buffered data from a nonzero literal allocated source row.
The source coefficient transport is exact; support, Mellin profiles,
clipping, slot reindexing, and logarithmic length are proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification HeckeDyadic ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedProfile CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentPrimeSlot CenteredMomentHeckeExpansion
open CenteredMomentDivisorRectangle
local notation "O" => HeckeFamily.O

def allocationSlotEmbedding {ι Slot : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι ↪ Slot) (D : Ideal O)
    (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) :
    liveIndices D allocation ↪ Slot where
  toFun i := f i.val
  inj' := fun _ _ h => Subtype.ext (f.injective h)

/-- Uniform profiles are chosen from the fixed original plain functions.
Every later nonzero allocated source row has concrete data on a subset of
the original slot type, with exact norm and the full reduction in length. -/
theorem actual_source_allocated_buffered
    (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hs₁ : Function.support W₁ ⊆ Icc a₁ b₁) (hW₁ : ContDiff ℝ ∞ W₁)
    (hs₂ : Function.support W₂ ⊆ Icc a₂ b₂) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ {ι Slot : Type*} [Fintype ι] [DecidableEq ι] [Fintype Slot] [DecidableEq Slot]
        (f : ι ↪ Slot) (orders : Finset Slot → ℕ) (edge e : ℝ), edge ≤ 1 → e ≤ 1/1000 →
      ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
        (η : Character) (w : NonzeroElement) (parent : JointParentLabel η)
        (N : NaturalRow parent.val w.val) (puncture : Ideal O) (hpuncture : puncture ≠ 0)
        (source : Character) (m A z : O) (t : ℝ),
      (∀ I : Ideal O, rowWeight source m A z t I =
        rowWeight parent.val (fixedBadMask*idealGenerator puncture) 1 w.val t I) →
      ∀ (D : Ideal O) (allocation : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
        (Z d X₁ X₂ : ℝ) (η₀ : Slot → Character) (V : Slot → ℝ → ℂ)
        (b : Slot → ℝ) (P : ι → ℝ) (bin : ℕ),
      1 < Z → d ≠ 0 → 1 < Z^d → 0 < X₁ → 0 < X₂ → (∀ i, 0 < P i) →
      allocatedPositiveRow source m A z t (fun i => primePool M H (b (f i)) (P i))
        (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
        D allocation W₁ W₂ X₁ X₂ ≠ 0 →
      ∃ P₁ P₂ : BufferedPlainProfile
          (orders (embeddedSlots (allocationSlotEmbedding f D allocation))) C edge e,
        P₁.W = dilated W₁ (clipDilation (X₁/(Ideal.absNorm (selectedPlain D allocation 0) : ℝ))) ∧
        P₂.W = dilated W₂ (clipDilation (X₂/(Ideal.absNorm (selectedPlain D allocation 1) : ℝ))) ∧
        P₁.σ = 0 ∧ P₂.σ = 0 ∧ P₁.freq = t ∧ P₂.freq = t ∧
        let data := embeddedBufferedData (allocationSlotEmbedding f D allocation) orders C edge e
          (allocatedBufferedData parent N puncture hpuncture D allocation P₁ P₂ Z d X₁ X₂ P t bin)
        ‖allocatedPositiveRow source m A z t (fun i => primePool M H (b (f i)) (P i))
          (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i)) P
          D allocation W₁ W₂ X₁ X₂‖ = ‖data.value M H η₀ V b Z d‖ ∧
        d*data.length ≤ Real.logb Z (X₁*X₂*∏ i, P i)-
          Real.logb Z (formalReductionFactor D allocation P)+Real.logb Z (max 1 b₁*max 1 b₂) := by
  obtain ⟨C,hC,hprofiles⟩ := actual_allocated_buffered_profiles W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hW₁ hs₂ hW₂
  refine ⟨C,hC,?_⟩
  intro ι Slot instι instDι instSlot instDSlot f orders edge e hedge he M instM H
    η w parent N puncture hpuncture source m A z t hrow D allocation
    Z d X₁ X₂ η₀ V b P bin hZ hd hbase hX₁ hX₂ hP hn
  have hsupport := allocated_positive_support source m A z W₁ W₂ _ _ P D allocation
    t X₁ X₂ b₁ b₂ hX₁ hX₂ (fun _ h => (hs₁ h).2) (fun _ h => (hs₂ h).2) hn
  let f' := allocationSlotEmbedding f D allocation
  obtain ⟨P₁,P₂,h₁,h₂,hσ₁,hσ₂,ht₁,ht₂,hnorm⟩ :=
    hprofiles (orders (embeddedSlots f')) edge e hedge he M H η w parent N puncture hpuncture
      D allocation Z d X₁ X₂ (fun i => η₀ (f i)) (fun i => V (f i))
      (fun i => b (f i)) P t bin hbase hX₁ hX₂ hP hsupport.1 hsupport.2
  refine ⟨P₁,P₂,h₁,h₂,hσ₁,hσ₂,ht₁,ht₂,?_⟩
  dsimp only
  constructor
  · rw [embeddedBufferedData_value]
    have heq := allocatedPositiveRow_transport source parent.val m A z
      (fixedBadMask*idealGenerator puncture) 1 w.val t hrow
      (fun i => primePool M H (b (f i)) (P i))
      (fun i I => idealCoeff (η₀ (f i)).inverse I*V (f i) ((I.absNorm : ℝ)/P i))
      P D allocation W₁ W₂ X₁ X₂
    rw [heq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm
  · rw [embeddedBufferedData_length]
    exact allocatedBufferedData_length_bound parent N puncture hpuncture D allocation P₁ P₂
      Z d X₁ X₂ b₁ b₂ P t bin hZ hd hX₁ hX₂ hP hsupport.1 hsupport.2

#print axioms actual_source_allocated_buffered
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointSourceBuffered -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.CertifiedExistence ; sha256 58808018650ed933d7ee561ec40dfedc6ef008a67839b957e7a64c2c5d437fa9 -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/CertifiedExistence.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: κ ≥ 7/10 positive stages; complete zero-slot endpoint supplied independently.
-/



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.Cycle25CenteredMomentEnergyCertifiedExistence
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open Cycle25CenteredMomentEnergyCappedAnalyticSuccessor CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(7/10:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤ count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k< count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(_hrad:0< radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(7/10:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl

end SevenEighths.Cycle25CenteredMomentEnergyCertifiedExistence

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.CertifiedExistence -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.ActualBin ; sha256 260397e2359b2235f00cb5fb7bac0e3922fccbb6352e55fe344c12f961a88eaf -/
section



/-! The actual physical numerator on a finite amplitude bin. Its only moment
input is a fourth moment of the original row-character polynomial on active
scales; the coefficient masses and all infinite sums are proved here. -/
noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

def labelPolynomialPacket {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) (u : FreeRow)
    (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Yp : ι→ℝ) (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  (Y:ℂ)^(-(1/2:ℂ))*∑'e : LabelPacketIndex S u T,
    labelPacketCoefficient S hS η u T hT
      (fun i P=> physicalSlotWeight P.val (W i) (Yp i) z) x z e*
    (labelPacketScale S u T e:ℂ)^(-(1/2:ℂ))*
    HeckeDyadic.polynomial (rowCharacter S hS.prime u) false W1
      (Y/(labelPacketScale S u T e:ℝ)) 0 0

theorem actual_label_packet_bin_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (kap massEps cp dp Bp : ℝ) (hkap : 7/10 ≤ kap) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤ Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤ Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤ alpha → alpha≤1 → 0< eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0< a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0< Y →
      ∀(U xi : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L zcap delta loss momentEps Ccount Cmoment : ℝ),
      1≤ U → 0≤ xi → 1≤ Ccount → 1≤ Cmoment → 0≤ q → q≤ delta/2 →
      0≤ delta/4 → delta/4≤1 →
      1-alpha-6*eps≤1/2-delta/4 → -(1/100:ℝ)≤1/2-delta/4 →
      1+firsteps≤ x.re+(1/2-delta/4) → 0< Ccond →
      (∀i,0≤ Cu i) → (∀i,Cu i≤ Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤ U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤ Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*selectedCapacity kap zcap ((j:ℝ)*xi+xi)-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤ U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤ b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤ Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*zcap/2+(3*R+1+momentEps)/4+loss/2+delta*xi/4) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY U xi n Cu Ccond Q P
    R q L zcap delta loss momentEps Ccount Cmoment hU hxi hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=> physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0< N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0< M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=> Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ)<(Ideal.span {(u i).val}:Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast FiniteConductor.absNorm_le_of_le (Ideal.le_radical (I := (Ideal.span {(u i).val}:Ideal O)))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/4) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/4))≤ M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤ x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤ b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤ b*Y) :
      max 1 (Lc i*N i e)≤ U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := packet_weighted_bins (fun i=> labelPacketBase S (u i) T Pbase) A Sp N hNp Lc kap U xi n
    (fun i e=> N i e≤ b*Y) Q P R q L zcap delta loss momentEps Ccount Cmoment M hkap hM hU hxi hc hm
    hq hqdelta hcard hzoff hupp hseries (fun i=>(hms i).1) hmassU hselected hfull hselection
  have heq : (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) =
      Y^(-(1/2:ℝ))*(∑i,‖(∑'e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold labelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)

theorem errorLabelNumerator_eq_packet {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (J : Finset (Fin K)) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤ P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0< Y) :
    errorLabelNumerator S hS η u J T hT W Yp x z W1 Y =
      labelPolynomialPacket S hS η u (fun i:J=> T i.val) (fun i=> hT i.val)
        (fun i=> W i.val) (fun i=> Yp i.val) x z W1 Y := by
  exact errorLabelNumerator_reconstruction S hS firsteps hfirst η u hrow J T hT hdis hη hQ
    W Yp x z hx hz hmargin W1 a b ha hsupp hW Y hY

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.ActualBin -/

/- BEGIN ORIGINAL MODULE Global.Low.Reflection.LowMemberGeometry ; sha256 71ed9e498856ffd3c63bcc6fa88a8de96f6fe284af3937cadaba0fb9fc9d5832 -/
section



/-! Adapted from OpenAI/math family003, pinned original module Reflection.LowMemberGeometry.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace Submission20261012.Global
open OAI OAI.SevenEighths

namespace LowReflection
open InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem original_low_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0< lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤ Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0< C ∧ 1< Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤ Z → 0< Ck → 0< CO → 0< CH → 0< X → 0< QK → 0< QP →
      (Ideal.absNorm I:ℝ)≤ Ck*Z^((1-Submission20261012.Global.ell)-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤ O₀+η → normWidth Z Q≤η →
      0≤ d → d≤ Submission20261012.Global.ell → ell0≤ Submission20261012.Global.ell-d+η → 0≤ O₀ → za≤ ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤ Z^Lrow → (QP/2)≤ Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤ Z^Lcap → QK≤ Z^Lcap → QP≤ Z^Lcap → -saving≤((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤ Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤ Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤ QK → 2≤ QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤ QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤ QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(((1-Submission20261012.Global.ell)-d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  have hb (i : γ) := original_low_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤ degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤ CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0< CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1< ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0< Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end LowReflection

end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Low.Reflection.LowMemberGeometry -/

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFullWNormalized ; sha256 42d59ee3a3733d0f02e356d3f7de2267632024278ada3df10444ec6fa74bf2aa -/
section
/- Adapted from weighted upstream PR6; original proof structure retained. -/





open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transferPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_cube_fullW_arbitrary_saving
    (K : ℕ) (τ saving a b B ζ nu : ℝ)
    (hτ : 0 < τ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hζ : ζ ≤ 1/48) (hnu : 0 < nu)
    (e : ℝ) (he : 0 < e) (he' : e < 1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,0 < ell j) (hellinj : Function.Injective ell)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b)
    (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0 ≤ (W0 y).re) (hp1 : ∀y,0 ≤ (W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ≤ Z^((Submission20261012.Global.h:ℝ)+ζ)) →
      ∀(alpha base height : FreeRow→ℝ) (idx : FreeRow→ℕ),
      (∀u∈R,(51/100:ℝ) ≤ alpha u ∧ alpha u ≤ 1 ∧ 2 < base u ∧
        Z^τ ≤ height u ∧ height u ≤ (3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(idx u+1:ℕ)*base u) < alpha u+2*e) →
      let Y : Fin K→ℝ := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Y j)
      let hT := transferPoolOutside M H S K a b Y
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧
      ‖finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha height/normer-
        Cycle25.Weighted.FullWContour.finiteCentralFullWRows S hS hmax η R T hT WC Y W0 W1
          (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha height/normer‖ ≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ct,hCt,htransfer⟩ := finite_cube_fullW_arbitrary_saving
    (ι:=RayQuotient.Characters M H) K τ (saving+nu) b ζ B hτ (ha.trans_le hab) hζ hB
    e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Submission20261012.Global.LowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    hell hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Ct*Cn,mul_nonneg hCt hCn.le,?_⟩
  filter_upwards [hnormalizer,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=> a) (fun _=> b) ell (fun _=> ha) (fun _=> hab) hellinj,
    eventually_ge_atTop (1:ℝ)] with Z hnorm hdis hZ
  intro η R hR alpha base height idx hbin
  dsimp only at hnorm ⊢
  refine ⟨hnorm.1,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let Y : Fin K→ℝ := fun j=> Z^(ell j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Y j)
  let hT := transferPoolOutside M H S K a b Y
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) :
      (P.val.absNorm:ℝ) ≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ0 (ell j)) P hP).2
    simpa only [mul_comm] using hh
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hb := htransfer η Z hZ R hR T hT hdis ell hellsum hpool WC hWCB
    alpha base height idx (rayCubeFamily M H hH) hbin
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hb hnorm.2 (norm_nonneg _) (by positivity)).trans_eq
  have hp : Z^(-(saving+nu))*Z^nu=Z^(-saving) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  calc
    _ = (Ct*Cn*(η.modulus.absNorm:ℝ)^2)*(Z^(-(saving+nu))*Z^nu) := by ring
    _ = _ := by rw [hp]

end Submission20261012.Global.HighRowFamily
end

end
/- END ORIGINAL MODULE Global.Transport.CubeFullWNormalized -/

/- BEGIN ORIGINAL MODULE Global.Transport.NormalizedTransport ; sha256 63a48c93bbada5cad9470048d94a6321f2fa78a9234dd5be0fea2dd022e1148b -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/






open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem transportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : Submission20261012.Global.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=Submission20261012.Global.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := transportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (Submission20261012.Global.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+Submission20261012.Global.b)/6) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((Submission20261012.Global.h:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z e alpha height/normer‖≤
        C*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-1/4000+nu)+
          Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6+e-Submission20261012.Global.theta*ellMin)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := Submission20261012.Global.LowNormalizer.actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=> hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := Submission20261012.Global.Transport.PrincipalNormalized.actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  dsimp only [Submission20261012.Global.Transport.PrincipalSignal.signalShift] at hprincipal
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0 ≤ D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=> a) (fun _=> b) ell (fun _=> ha) (fun _=> hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := transportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖ ≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : ProbePhysical.PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ) ≤ b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  have hbinsHi (u : FreeRow) : (51/100:ℝ)+e*grid u ≤ 7/8 := by
    by_cases hgt : (51/100:ℝ) < 51/100+e*grid u
    · obtain ⟨j,s,hzero,hpole,has,_⟩ := (hbins u).2.2.2.2.2 hgt
      have hs : 0 < s.re := by linarith
      have hpole' : s ≠ 1 ∨ (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue ≠ 1 := by tauto
      exact has.trans ((HeckeZeroSupremum.zero_re_le_beta _ hs hpole' hzero).trans hβ)
    · linarith
  refine ⟨hnorm.1,idx,grid,hlabels,(fun u=>⟨(hbins u).1,hbinsHi u,(hbins u).2.2⟩),hray,?_⟩
  have hh := normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  simp only [neg_div] at hh ⊢
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ ((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D ≤ D+Cp := by linarith
  have h2 : Cp ≤ D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6-1/4000+nu)+Z^(HeckeZeroSupremum.beta-(4+Submission20261012.Global.b)/6+e-Submission20261012.Global.theta*ellMin)) := by
      gcongr
    _ = _ := by ring

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.NormalizedTransport -/
