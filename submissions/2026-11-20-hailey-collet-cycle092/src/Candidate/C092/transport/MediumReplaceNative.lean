/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
P4 on the exact original Batch rows, with a derived shorter-ordinary bound.
The original Mellin polynomial, same-zero witness and all weights persist. -/
import Candidate.C092.transport.MediumReplaceUpper
import Candidate.C092.transport.SignedEnergy

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open HeckeDyadic HeckeDetectorBatch HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.Assembly
open QRH.Cycle092.MediumWitness
namespace QRH.Cycle092.MediumReplace
variable [Geometry.Parameters]

/-- Actual original shorter polynomials, with their separate profiles and
frequencies, on precisely the rows being compared. These are analytic profile
controls, not assumed pointwise polynomial or energy bounds. -/
structure ShortDataOn (D : BaselineData) (F : BaselineSourceData D)
    (η : Character) (Z τ d y : ℝ) (idx grid : FreeRow → ℕ)
    (order : ℕ) (profileBound : ℕ → ℝ) (rows : Finset FreeRow) where
  label : FreeRow → Sum Bool (RayQuotient.Characters F.modulus ⊤)
  profile : FreeRow → ℝ → ℂ
  lower : FreeRow → ℝ
  upper : FreeRow → ℝ
  sigma : FreeRow → ℝ
  frequency : FreeRow → ℝ
  lower_pos : ∀ u ∈ rows,0 < lower u
  support : ∀ u ∈ rows,Function.support (profile u) ⊆ Icc (lower u) (upper u)
  smooth : ∀ u ∈ rows,ContDiff ℝ ∞ (profile u)
  frequency_bound : ∀ u ∈ rows,|frequency u|+Z^τ/2 ≤ (3*idx u+2 : ℕ)*Z^τ
  mellin_two : ∀ u ∈ rows,∀ x ∈ Icc (1-(51/100+D.e*grid u)-6*D.e-sigma u) (2-sigma u),
    ∀ t : ℝ,(1+|t|)^2*‖mellin (profile u) ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2
  mellin_order : ∀ u ∈ rows,∀ x ∈ Icc (1-(51/100+D.e*grid u)-6*D.e-sigma u) (2-sigma u),
    ∀ t : ℝ,(1+|t|)^(order+2)*‖mellin (profile u) ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)

def ShortDataOn.value {D : BaselineData} {F : BaselineSourceData D}
    {η : Character} {Z τ d y : ℝ} {idx grid : FreeRow → ℕ}
    {order : ℕ} {profileBound : ℕ → ℝ} {rows : Finset FreeRow}
    (S : ShortDataOn D F η Z τ d y idx grid order profileBound rows) (u : FreeRow) : ℂ :=
  polynomial (originalFamily D F η u (S.label u)) false (S.profile u) (Z^y) (S.sigma u) (S.frequency u)

omit [Geometry.Parameters] in
/-- P4 including an explicit uniform upper constant. It does not divide by a
possibly zero original factor; the genuine ordinary spike is strictly positive. -/
theorem supported_replace (U V a ε cutoff T allowance C y loss : ℝ)
    {Label : Type*} {χ : Label → Character} {i : ℕ}
    (w : SupportedWitness χ (U^V) a ε cutoff T allowance i)
    (A_y A_n Q : ℂ) (reverse : Bool) (hU : 0 < U) (hC : 0 ≤ C)
    (hy : ‖A_y‖^2 ≤ C*U^((2*a-1)*y+loss)) :
    ‖A_n*A_y*Q‖^2 ≤ C*U^((2*a-1)*(y-V*w.m)+loss+2*V*ε)*
      ‖A_n*QRH.Cycle092.SignedEnergy.oriented reverse
        (QRH.Cycle092.SignedEnergy.actualPlain w)*Q‖^2 := by
  let f := (2*a-1)*(y-V*w.m)+loss+2*V*ε
  have hw : U^(V*((2*a-1)*w.m-2*ε)) ≤
      ‖QRH.Cycle092.SignedEnergy.actualPlain w‖^2 := by
    rw [Real.rpow_mul hU.le]
    exact w.plain_spike
  have hn := mul_le_mul_of_nonneg_left hw (Real.rpow_pos_of_pos hU f).le
  rw [←Real.rpow_add hU,
    show f+V*((2*a-1)*w.m-2*ε)=(2*a-1)*y+loss by dsimp [f];ring] at hn
  have hy' := hy.trans (mul_le_mul_of_nonneg_left hn hC)
  simp only [norm_mul,mul_pow,QRH.Cycle092.SignedEnergy.norm_oriented]
  calc
    _ ≤ ‖A_n‖^2 * (C*(U^f*‖QRH.Cycle092.SignedEnergy.actualPlain w‖^2))*‖Q‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy' (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by dsimp [f];ring

/-- The ordinary escape case and its original right dyadic label, on the
same original Batch. No independent witness or row set is selected. -/
def ordinaryEscapeRows {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε cutoff T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label Slot U a ε cutoff T allowance i)
    (r0 : ℝ) (K : Fin (dyadicLength U)) : Finset FreeRow :=
  B.rows.filter fun u => (B.witness u).r < r0 ∧ (B.witness u).right=K

omit [Geometry.Parameters] in
theorem ordinaryEscapeRows_spec {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε cutoff T allowance r0 : ℝ} {i : ℕ}
    (B : Batch M H Label Slot U a ε cutoff T allowance i) (hU : 1 < U)
    (K : Fin (dyadicLength U)) :
    ordinaryEscapeRows B r0 K ⊆ B.rows ∧
      ∀ u ∈ ordinaryEscapeRows B r0 K,
        (B.witness u).m=Real.logb U ((2 : ℝ)^K.val) ∧
        cutoff-r0-ε ≤ (B.witness u).m := by
  refine ⟨Finset.filter_subset _ _,?_⟩
  intro u hu
  have h := (Finset.mem_filter.mp hu).2
  refine ⟨?_,?_⟩
  · rw [(B.witness u).toWitness.right_exponent hU,h.2]
  · linarith [(B.witness u).product_length_lower,h.1]

/-- The actual selected source supplies the shorter-factor upper, while the
very same Batch supplies the attaining ordinary lower. Both sums use exactly
s, which may include any additional frozen masks/keep/case restrictions.
The factor A_n and the complete original marked Q remain literally unchanged.
The charge is nu*(y-d*m)+3*d*epsilon, with nu=2*bandLower-1. -/
theorem original_batch_P4 (D : BaselineData) (F : BaselineSourceData D)
    (τ : ℝ) (hτ : 0 < τ) (hheight : 4*τ < (1/200 : ℝ)*D.cost)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k,0 ≤ profileBound k) :
    ∃ order : ℕ,∃ C : ℝ,0 < C ∧ ∀ (η : Character) (n : ℕ),
      ∀ᶠ Z : ℝ in atTop,1 < Z ∧
      ∀ (padding d threshold lowPay cutoff y m : ℝ) (idx grid : FreeRow → ℕ),
        (1/200 : ℝ) ≤ d → d ≤ 7/8 → 0 ≤ y → y/d ≤ 22 →
        ProbeAssembly.selected D F padding τ n η Z idx grid →
      ∀ (i k : ℕ) (z : FreeRow → Fin D.N → ℂ),
      ∀ B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤))
        (Fin D.N) (Z^d) (bandLower D k) D.ε cutoff (Z^τ)
          ((Z^d)^(τ/(2*(7/8 : ℝ)))) i,
        B.rows ⊆ sharedRows D F (Z^(Geometry.h+padding)) Z d threshold lowPay idx grid z i k →
      ∀ s : Finset FreeRow,s ⊆ B.rows →
      ∀ S : ShortDataOn D F η Z τ d y idx grid order profileBound s,
      ∀ (A_n Q : FreeRow → ℂ) (weight : FreeRow → ℝ) (reverse : FreeRow → Bool),
        (∀ u ∈ s,0 ≤ weight u) → (∀ u ∈ s,(B.witness u).m=m) →
        ∑ u ∈ s,weight u*‖A_n u*S.value u*Q u‖^2 ≤
          C*Z^((2*bandLower D k-1)*(y-d*m)+3*d*D.ε)*
            ∑ u ∈ s,weight u*‖A_n u*QRH.Cycle092.SignedEnergy.oriented (reverse u)
              (QRH.Cycle092.SignedEnergy.actualPlain (B.witness u))*Q u‖^2 := by
  obtain ⟨order,C,hC,hupper⟩ := original_short_upper D F τ hτ hheight profileBound hprofile
  refine ⟨order,C,hC,?_⟩
  intro η n
  filter_upwards [hupper η n] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro padding d threshold lowPay cutoff y m idx grid hd hd' hy hy' hsel i k z B hB s hs S A_n Q weight reverse hweight hsame
  have hdpos : 0 < d := (by norm_num : (0:ℝ)<1/200).trans_le hd
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hscale : (Z^d)^(y/d)=Z^y := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hrow := Finset.mem_filter.mp (hB (hs hu))
  have hi : idx u=i := hrow.2.2.2.2.1
  have hk : grid u=k := hrow.2.2.2.2.2
  have hup := hZ.2 padding d (Z^(Geometry.h+padding)) idx grid hd hd' hsel u hrow.1
    hrow.2.1 hrow.2.2.1 (S.label u) (S.profile u) (S.lower u) (S.upper u) (y/d) (S.sigma u) (S.frequency u)
    (S.lower_pos u hu) (S.support u hu) (S.smooth u hu) (div_nonneg hy hdpos.le) hy'
    (S.frequency_bound u hu) (S.mellin_two u hu) (S.mellin_order u hu)
  rw [hscale,←Real.rpow_mul hZpos.le] at hup
  have hex : d*((2*(51/100+D.e*grid u)-1)*(y/d)+D.ε)=
      (2*bandLower D k-1)*y+d*D.ε := by rw [hk];unfold bandLower;field_simp [hdpos.ne']
  rw [hex] at hup
  have hpoint := supported_replace Z d (bandLower D k) D.ε cutoff (Z^τ)
    ((Z^d)^(τ/(2*(7/8 : ℝ)))) C y (d*D.ε) (B.witness u) (S.value u) (A_n u) (Q u)
    (reverse u) hZpos hC.le hup
  rw [hsame u hu] at hpoint
  have hex' : (2*bandLower D k-1)*(y-d*m)+d*D.ε+2*d*D.ε=
      (2*bandLower D k-1)*(y-d*m)+3*d*D.ε := by ring
  rw [hex'] at hpoint
  exact (mul_le_mul_of_nonneg_left hpoint (hweight u hu)).trans_eq (by ring)

end QRH.Cycle092.MediumReplace
#print axioms QRH.Cycle092.MediumReplace.supported_replace
#print axioms QRH.Cycle092.MediumReplace.original_batch_P4
