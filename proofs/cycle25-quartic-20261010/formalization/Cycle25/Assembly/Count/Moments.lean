import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

/-! Cycle25 moment contract. The analytic moments are actual physical row sums,
with the original dictionary; κplain is separate from inverse amplification. -/
namespace OAI.SevenEighths.Cycle25DetectorRawFiber
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open HeckeDetectorCoefficientTransfer
open Set HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDetectorPlainFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain c κinverse C height εm : ℝ) : Prop where
  original : HeckeDetectorRawFiber.Moments F 0 c κinverse C height εm
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*κplain*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)

theorem plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm : ℝ} (moments : Moments F κplain c κinverse C height εm)
    (hU : 1<U) (ha : 1/2≤a) (hκ : 0≤κplain) (hC : 0≤C) (hh : 0≤height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (z : ℝ) (hz : 0≤z) (hz' : z≤7/37) (hcap : 2*F.m+6*κplain*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κplain εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hκ hC hh hf hcap moments.plain_marked

structure BaseMoments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

def MarkedPlainMoment (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (κplain C height εm : ℝ) : Prop := ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*κplain*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤C*U^(1+εm)


theorem Moments.of_fields (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {κplain c κinverse C height εm : ℝ} (hk : κplain≤3/4)
    (base : BaseMoments F c κinverse C height εm)
    (plain : MarkedPlainMoment F κplain C height εm) :
    Moments F κplain c κinverse C height εm := by
  refine ⟨⟨base.inverse_raw,base.inverse_marked,?_,base.plain_unmarked⟩,plain⟩
  intro selected hselected hcap
  apply plain selected hselected
  have hs : 0≤∑s∈selected,F.widths s := Finset.sum_nonneg (fun s hs=>(F.widths_pos s (hselected hs)).le)
  have hh := mul_le_mul_of_nonneg_right hk hs
  norm_num at hcap
  nlinarith
end
end OAI.SevenEighths.Cycle25DetectorRawFiber
