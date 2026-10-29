/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.ParentMarkedPlain
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.PlainOrientation
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootHoleSlots
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch

/-! Actual rooted plain moment, supplied by the parent source. The moving
Euler holes are expanded before positivity, with one total small-power loss. -/
namespace Qrh.JointDetector.RepeatedMarks.ParentPlainBatch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped Classical BigOperators ContDiff SchwartzMap ComplexConjugate
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open CenteredMomentDetectorEnergyInitialState Cycle61Moment
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorCoefficientTransfer
open CenteredMomentDetectorPlainFiberSource
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
local notation "O" => HeckeFamily.O
variable {Slot Label : Type} [Fintype Slot] [DecidableEq Slot] [Fintype Label] [Nonempty Label]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The annular coefficient bound is uniform in all imaginary shifts. -/
theorem coefficient_bound (W : ℝ→ℂ) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (Cw : ℝ) (hCw : 0≤Cw) (hWb : ∀x,‖W x‖≤Cw)
    (η : Character) (P σ t : ℝ) (hσ : 0≤σ) (I : Ideal O) :
    ‖idealCoeff η I*HeckePrimeAnnular.annularWeight W P σ t I‖≤Cw := by
  have ha : ‖HeckePrimeAnnular.annularWeight W P σ t I‖≤Cw := by
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simpa [HeckePrimeAnnular.annularWeight,hz] using hCw
    · have hx := hWs hz
      have hxpos : 0<(I.absNorm:ℝ)/P := lt_of_lt_of_le zero_lt_one hx.1
      rw [HeckePrimeAnnular.annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
      have hp : ((I.absNorm:ℝ)/P)^(-σ)≤1 := by
        exact (Real.rpow_le_rpow_of_exponent_le hx.1 (by linarith)).trans_eq (Real.rpow_zero _)
      simpa only [Complex.neg_re,shift_re] using
        (mul_le_mul (hWb _) hp (Real.rpow_nonneg hxpos.le _) hCw).trans_eq (mul_one Cw)
  rw [norm_mul]
  exact (mul_le_mul (idealCoeff_norm_le_one η I) ha (norm_nonneg _) zero_le_one).trans_eq (one_mul Cw)

/-- A fixed smooth compactly supported slot profile has a fixed coefficient
bound, independent of every later character, slot, row and height. -/
theorem exists_profile_bound (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) : ∃Cw:ℝ,0<Cw ∧ ∀x,‖W x‖≤Cw := by
  have hb : BddAbove ((fun x:ℝ=>‖W x‖) '' Icc (1:ℝ) 2) :=
    isCompact_Icc.bddAbove_image hW.continuous.norm.continuousOn
  obtain ⟨C,hC⟩ := hb
  refine ⟨|C|+1,by positivity,?_⟩
  intro x
  by_cases hz : W x=0
  · simp only [hz,norm_zero]
    positivity
  · have hh : ‖W x‖≤C := hC ⟨x,hWs hz,rfl⟩
    linarith [le_abs_self C]

/-- The root precision is chosen only after the finite copied slot type.
It does not request a finer parent mesh. -/
theorem root_loss_budget {ε A : ℝ} (hε : 0<ε) (hA : 0≤A) (N : ℕ) :
    0<ε/(4*(A+1)*((N:ℝ)+1)) ∧
    2*(N:ℝ)*A*(ε/(4*(A+1)*((N:ℝ)+1)))≤ε/2 := by
  have hN : 0≤(N:ℝ) := Nat.cast_nonneg _
  constructor
  · positivity
  · rw [show 2*(N:ℝ)*A*(ε/(4*(A+1)*((N:ℝ)+1)))=
        ε*(2*(N:ℝ)*A)/(4*(A+1)*((N:ℝ)+1)) by ring]
    apply (div_le_iff₀ (by positivity)).mpr
    have hd : 2*(N:ℝ)*A≤2*(A+1)*((N:ℝ)+1) := by nlinarith
    have he := mul_le_mul_of_nonneg_left hd hε.le
    nlinarith only [he]

/-- Complete actual rooted plain raw field. The only source hypothesis is
its literal previously proved parent face. There is no masked moment premise. -/
theorem field_for_label
    (B L c mesh εm Aroot : ℝ) (hL : 0≤L) (hεm : 0<εm) (hAr : 0≤Aroot)
    (hsource : UnitFaceSource (globalFace B L c) mesh (εm/2))
    (base anchor : Label→Character) (bad : Label→Ideal O) (label : Label)
    (hQM : bad label≤M) (hQ0 : internalQ (bad label) (anchor label)≠0)
    (hQt : internalQ (bad label) (anchor label)≠⊤)
    (hQ72 : internalQ (bad label) (anchor label)≤Ideal.span {(72:O)})
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Icc (1:ℝ) 2)
    (Cw : ℝ) (hCw : 0≤Cw) (hWb : ∀x,‖W x‖≤Cw)
    (bΦ : ℝ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ U : ℝ in atTop,1<U ∧
      ∀N : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot,
      (∀s∈N.slots,N.widths s≤mesh) →
      ∀(rows : Finset FreeRow),rows⊆N.rows →
      ∀(selected : Finset Slot),selected⊆N.slots →
      ∀(χ : FreeRow→Character)(reverse : Bool),
      (∀u∈rows,∀I,idealCoeff (χ u) I=
        if reverse then conj (idealCoeff (N.family u label) I) else idealCoeff (N.family u label) I) →
      ∀m height : ℝ,0≤m → 0≤height →
      (∀s∈selected,|N.commonHeight+N.relativeHeight s|≤height) →
      (∑s∈selected,N.widths s)≤c → 2*m+L*(∑s∈selected,N.widths s)≤B →
      ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) (U^m) σd freq*
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) (U^m) σd freq*
        (∏s∈selected,N.Q u s)‖^2)≤C*(1+height)^J*U^(1+εm) := by
  obtain ⟨J,Cp,hCp,hfield⟩ := ParentMarkedPlain.plain_energy_of_unit_source (α:=Slot)
    M H hH B L c mesh (εm/2) hL hsource W hW hWs bΦ hrad
    (base label) (anchor label) (bad label) hQM hQ0 hQt hQ72
  let n : ℕ := Fintype.card Slot
  let δ : ℝ := εm/(4*(Aroot+1)*((n:ℝ)+1))
  have hδ : 0<δ := (root_loss_budget hεm hAr n).1
  have hδbudget : 2*(n:ℝ)*Aroot*δ≤εm/2 := (root_loss_budget hεm hAr n).2
  obtain ⟨Cd,hCd,hdiv⟩ := RootHoleSlots.removed_primes_card_subpower δ hδ
  let K : ℝ := max 1 (Cd*Cw)
  have hK : 1≤K := le_max_left _ _
  let R : ℝ := (2:ℝ)^n
  have hR : 0<R := by dsimp [R];positivity
  let C : ℝ := R^2*K^(2*n)*Cp
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hfield] with U hU
  refine ⟨hU.1,?_⟩
  intro N hwm rows hrows selected hselected χ reverse hcoeff m height hm hh hv hcap hbudget
  have hUp : 0<U := zero_lt_one.trans hU.1
  let E : ℝ := K*U^(Aroot*δ)
  have hE : 1≤E := one_le_mul_of_one_le_of_one_le hK
    (Real.one_le_rpow hU.1.le (mul_nonneg hAr hδ.le))
  let β : Slot→Ideal O→ℂ := fun s I=>
    idealCoeff (relativeCharacter M H hH (anchor label) (N.rays label s)) I*
      HeckePrimeAnnular.annularWeight W (U^(N.widths s)) (N.sigma s)
        (N.commonHeight+N.relativeHeight s) I
  let Qplain : Slot→FreeRow→ℂ := fun s u=>naturalSlot (N.family u label)
    (primePool M H 2 (U^(N.widths s))) (β s) (U^(N.widths s))
  let D : Slot→FreeRow→ℂ := fun s u=>naturalSlot (N.family u label)
    ((primePool M H 2 (U^(N.widths s))).filter (fun I=>¬IsCoprime I (N.root label)))
    (β s) (U^(N.widths s))
  have herror : ∀s∈selected,∀u∈rows,‖D s u‖≤E := by
    intro s hs u hu
    have hsw := N.widthsNonneg s (hselected hs)
    have hP : 1≤U^(N.widths s) := Real.one_le_rpow hU.1.le hsw
    have hβ : ∀I∈primePool M H 2 (U^(N.widths s)),‖β s I‖≤Cw := by
      intro I hI
      exact coefficient_bound W hWs Cw hCw hWb _ _ _ _ (by linarith [N.sigmaLower s (hselected hs)]) I
    have hd := RootHoleSlots.naturalSlot_hole_norm (N.family u label)
      (primePool M H 2 (U^(N.widths s))) (β s) (U^(N.widths s)) Cw (N.root label) hP hCw hβ
    have hc := hdiv (N.root label) (N.root_ne_zero label)
      (primePool M H 2 (U^(N.widths s))) (fun I hI=>(Finset.mem_filter.mp hI).2.1)
    have hrootpow : ((N.root label).absNorm:ℝ)^δ≤U^(Aroot*δ) := by
      calc _ ≤ (U^Aroot)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _) (N.root_norm label) hδ.le
        _ = _ := (Real.rpow_mul hUp.le _ _).symm
    calc ‖D s u‖ ≤ _ := hd
      _ ≤ (Cd*((N.root label).absNorm:ℝ)^δ)*Cw := mul_le_mul_of_nonneg_right hc hCw
      _ ≤ E := by
        dsimp [E]
        have h1 := mul_le_mul_of_nonneg_left hrootpow (mul_nonneg hCd.le hCw)
        have h2 := mul_le_mul_of_nonneg_right (le_max_right 1 (Cd*Cw))
          (Real.rpow_nonneg hUp.le (Aroot*δ))
        nlinarith
  have hidentity : ∀u∈rows,∀s∈selected,‖N.Q u s‖=‖Qplain s u-D s u‖ := by
    intro u hu s hs
    rw [N.plainIdentity u (hrows hu) label s (hselected hs)]
    exact congrArg (fun z : ℂ => ‖z‖) (RootHoleSlots.naturalSlot_excluded_eq_sub (N.family u label)
      (primePool M H 2 (U^(N.widths s))) (β s) (U^(N.widths s))
      (N.root label) (N.root_ne_zero label))
  have hraw : ∀j k : ℕ,j+k≤2 → ∀σd∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      (∑u∈rows,‖polynomial (N.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σd freq*
        polynomial (N.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σd freq*
        (∏s∈selected,N.Q u s)‖^2)≤C*(1+height)^J*U^(1+εm) := by
    intro j k hjk σd hσd freq hfreq
    let P := fun u=>polynomial (N.family u label) false ((logProfile^[j]) positiveAnnular) (U^m) σd freq*
      polynomial (N.family u label) false ((logProfile^[k]) positiveAnnular) (U^m) σd freq
    have hsources : ∀s∈selected.powerset,∑u∈rows,‖P u*(∏i∈selected\s,Qplain i u)‖^2≤
        Cp*(1+height)^J*U^(1+εm/2) := by
      intro s hs
      let keep := selected\s
      have hk : keep⊆N.slots := Finset.sdiff_subset.trans hselected
      have hsum : (∑i∈keep,N.widths i)≤∑i∈selected,N.widths i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun i hi hni=>(N.widthsNonneg i (hselected hi)))
      have he := hU.2 rows (fun u:FreeRow=>u.val) Subtype.val_injective (fun u=>N.family u label)
        (fun u hu=>N.elementCoefficients u (hrows hu) label)
        (fun u hu=>N.retained u (hrows hu) label) (fun u hu=>N.embeddingNorm u (hrows hu))
        m hm keep (fun i=>N.rays label i.val) (fun i=>N.widths i.val)
        (fun i=>N.sigma i.val) (fun i=>N.commonHeight+N.relativeHeight i.val) height
        (fun i=>N.widthsNonneg i.val (hk i.property))
        (fun i=>hwm i.val (hk i.property))
        (fun i=>N.sigmaLower i.val (hk i.property)) (fun i=>N.sigmaUpper i.val (hk i.property)) hh
        (fun i=>hv i.val (Finset.sdiff_subset i.property))
        (by simpa only [Finset.sum_coe_sort] using hsum.trans hcap)
        (by have hhL := mul_le_mul_of_nonneg_left hsum hL
            simpa only [Finset.sum_coe_sort] using (show 2*m+L*(∑i∈keep,N.widths i)≤B by linarith))
        j k hjk σd hσd freq (abs_le.mpr hfreq)
      have he' : (∑u∈rows,‖P u*(∏i:keep,Qplain i.val u)‖^2)≤
          Cp*(1+height)^J*U^(1+εm/2) := he
      convert he' using 1
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.prod_coe_sort keep (fun i=>Qplain i u)]
    have he := RootHoleExpansion.product_perturbation_moment selected rows P Qplain D E
      (Cp*(1+height)^J*U^(1+εm/2)) hE herror hsources
    have he' : (∑u∈rows,‖P u*(∏s∈selected,N.Q u s)‖^2)≤
        (selected.powerset.card:ℝ)^2*E^(2*selected.card)*(Cp*(1+height)^J*U^(1+εm/2)) := by
      convert he using 1
      apply Finset.sum_congr rfl
      intro u hu
      simp only [norm_mul,norm_prod]
      congr 2
      exact Finset.prod_congr rfl (fun s hs=>hidentity u hu s hs)
    have hcard : selected.card≤n := Finset.card_le_univ _
    have hps : (selected.powerset.card:ℝ)≤R := by
      rw [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard
    have hepow : E^(2*selected.card)≤E^(2*n) :=
      pow_le_pow_right₀ hE (Nat.mul_le_mul_left _ hcard)
    have hbound0 : 0≤Cp*(1+height)^J*U^(1+εm/2) := by positivity
    apply he'.trans
    calc
      _ ≤ R^2*E^(2*n)*(Cp*(1+height)^J*U^(1+εm/2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hps 2) hepow
            (pow_nonneg (zero_le_one.trans hE) _) (sq_nonneg _)) hbound0
      _ = C*(1+height)^J*U^(1+εm/2+2*(n:ℝ)*Aroot*δ) := by
        have hr : (U^(Aroot*δ))^(2*n)=U^(2*(n:ℝ)*Aroot*δ) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
          congr 1
          push_cast
          ring
        dsimp [E,C]
        rw [mul_pow,hr,Real.rpow_add hUp (1+εm/2) (2*(n:ℝ)*Aroot*δ)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU.1.le (by linarith [hδbudget])) (by positivity)
  exact PlainOrientation.raw_moment χ (fun u=>N.family u label) reverse rows hcoeff
    (fun u=>∏s∈selected,N.Q u s) (U^m) height (C*(1+height)^J*U^(1+εm))
    (Real.rpow_pos_of_pos hUp _) hraw

end
end Qrh.JointDetector.RepeatedMarks.ParentPlainBatch
#print axioms Qrh.JointDetector.RepeatedMarks.ParentPlainBatch.field_for_label
