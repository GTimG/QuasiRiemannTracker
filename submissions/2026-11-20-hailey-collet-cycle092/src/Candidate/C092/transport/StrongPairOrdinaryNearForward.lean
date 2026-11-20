/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Forward lengths and genuine conductor-bank choice on the original regular core. -/
import Candidate.C092.transport.StrongPairOrdinaryNearHetero

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open ConcretePrimeRowBridge ProbeHighRowFamily HeckeRowClosure
open CenteredMomentEnergyBands CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Record12518109Source QRH.Record12518109Existence
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O

/-- Increasing the source conductor scale and freezing a lower bank radius
preserves the true long polynomial. No long length is enlarged or replaced. -/
theorem near_forward_long_cap {U X n d radius : ℝ}
    (hU : 0 < U) (hn : 0 ≤ n) (hr : 0 < radius) (hrd : radius ≤ d)
    (hX : length U X ≤ n) :
    length (U^d) X ≤ n/radius := by
  rw [length_rpow_base U X d hU]
  exact (div_le_div_of_nonneg_right hX (hr.trans_le hrd).le).trans
    (div_le_div_of_nonneg_left hn hr hrd)

/-- The genuine witness's ordinary cap is a forward upper cap, while its
actual length remains in P4's substitution debit. -/
theorem near_forward_witness_cap {U d n m B radius : ℝ}
    (hU : 1 < U) (hd : 0 < d) (hm : 0 ≤ m) (hB : m ≤ B) :
    length (U^d) ((U^d)^m) ≤ nearOrdinaryCap n B radius := by
  have hbase : 1 < U^d := Real.one_lt_rpow hU hd
  unfold length
  rw [max_eq_right (Real.one_le_rpow hbase.le hm),Real.logb_rpow (zero_lt_one.trans hbase) (ne_of_gt hbase)]
  exact hB.trans (near_cap_dominates _ _ _)

/-- The final analytic constant is uniform over every later retained set,
including the exact empty-complement case. -/
theorem near_erased_constant {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) {C : ℝ} (hC : 0 ≤ C) :
    C^(Finset.univ\F).card ≤ (max 1 C)^(Fintype.card Slot) := by
  have hcard : (Finset.univ\F).card ≤ Fintype.card Slot := by
    simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ (Finset.univ\F))
  exact (pow_le_pow_left₀ hC (le_max_right 1 C) _).trans
    (pow_le_pow_right₀ (le_max_left 1 C) hcard)

variable (M : Ideal O) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_StrongPairOrdinaryNearForward_92f5d9c50dc12995_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M ≤ Hr)

/-- The actual source-side conductor theorem and the early restored source
bank choose their d and (radius,cap) together. The original norm radius V
remains in the kept finite core; all dictionary labels have conductor U^d. -/
theorem ordinary_near_core_bank (η η₀ : Character) (Q : Ideal O)
    (Vmax δ gap m0 : ℝ) (hmax : (98/100:ℝ) ≤ Vmax) (hδ : 0 < δ)
    (bank : Finset (ℝ×ℝ))
    (hnet : ∀ d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃ p∈bank,p.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-p.1 < gap ∧ m ≤ p.2 ∧ p.2-m < gap) :
    ∃ conductorBank : Finset ℝ,
      (∀ d∈conductorBank,(98/100:ℝ)+2*δ ≤ d ∧ d ≤ Vmax+3*δ) ∧
    ∃ bΦ : ℝ,2 ≤ bΦ ∧ ∃ hs : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ,
    ∀ᶠ U : ℝ in atTop,∃ hU : 1<U,∃ hη : (η.modulus.absNorm:ℝ) ≤ U^δ,
    ∀ V m : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax → m0 ≤ m → m ≤ 51/100 →
    ∃ d∈conductorBank,∃ p∈bank,V+2*δ ≤ d ∧ d ≤ V+3*δ ∧
      p.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-p.1 < gap ∧ m ≤ p.2 ∧ p.2-m < gap ∧
      ∀ (u : FreeRow) (hV : 0 ≤ V),rowNorm u ≤ U^V →
      let st := regularState η Q radialMajorant bΦ U V δ hU.le hV hδ.le hs radialMajorant_nonneg hη
      ∀ (F : NaturalRow st.character u.val) j,((family M Hr hHr st η₀ F j).modulus.absNorm:ℝ) ≤ U^d := by
  obtain ⟨cbank,hcb,bΦ,hbΦ,hs,hsrc⟩ := source_core_conductors M Hr hHr η η₀ Q (98/100) Vmax δ
    (by norm_num) hmax hδ
  refine ⟨cbank,hcb,bΦ,hbΦ,hs,?_⟩
  filter_upwards [hsrc] with U hsrc
  obtain ⟨hU,hη,hsrc⟩ := hsrc
  refine ⟨hU,hη,?_⟩
  intro V m hV hVmax hm hm'
  obtain ⟨d,hd,hVd,hdV,hcore⟩ := hsrc V hV hVmax
  obtain ⟨p,hp,hpd,hgap,hmB,hBgap⟩ := hnet d m (by linarith) hm hm'
  exact ⟨d,hd,p,hp,hVd,hdV,hpd,hgap,hmB,hBgap,hcore⟩

#print axioms near_erased_constant
#print axioms near_forward_long_cap
#print axioms near_forward_witness_cap
#print axioms ordinary_near_core_bank
end
end QRH.Cycle092.StrongPair
