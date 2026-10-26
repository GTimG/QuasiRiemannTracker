/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
A fixed amplifier cell uses the actual annular prime pool with fixed bad-prime
exclusions. Its threshold is uniform in every marked slot type and moving
width below mesh. No moving puncture is removed from the pool. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ActualCoefficients
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Source.Pool
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplificationSlotGap
local notation "O" => HeckeFamily.O

/-- Every field concerns the same literal finite pool. The exponent a and
lower exponent ell are fixed before the eventual scale threshold. -/
structure FixedCellPoolData (P : Finset (Ideal O))
    (Z a ell mesh loss BD Bsource : ℝ) (depth : ℕ) : Prop where
  scale_gt_one : 1<Z
  nonempty : P.Nonempty
  card_power : Z^(a-loss)≤(P.card:ℝ)
  card_source : 2*(Bsource/ell)≤(P.card:ℝ)
  card_newton : 2*(BD/ell+(depth:ℝ)+1)≤(P.card:ℝ)
  prime : ∀Q∈P,Prime Q
  avoids_bad : ∀Q∈P,Q∉fixedBadPrimes
  norm_ge_sixteen : ∀Q∈P,(16:ℝ)≤Q.absNorm
  norm_lower : ∀Q∈P,Z^ell≤(Q.absNorm:ℝ)
  norm_upper : ∀Q∈P,(Q.absNorm:ℝ)≤Z^a
  marked_gap : 2*Z^mesh<Z^ell
  reciprocal : (P.card:ℝ)⁻¹≤Z^(-a+loss)

/-- The arbitrary fixed lower exponent ell only needs ell<a. -/
theorem eventually_annular_lower (a ell : ℝ) (ha : ell<a) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ Z^ell≤Z^a*(1/2:ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr ha)).eventually
    (eventually_ge_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hlarge hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hm := mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hz.le ell)
  rw [←Real.rpow_add hz,add_sub_cancel] at hm
  exact ⟨hZ,by linarith⟩

variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM≤H)

include hH in
/-- Fixed-cell constructor. BD and Bsource may be arbitrary real constants;
in particular this supplies the required nonnegative-budget case. The pool
remains annularPrimeIdeals minus the fixed Sbad throughout. -/
theorem eventually_fixed_cell_pool (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (a ell mesh loss BD Bsource : ℝ) (depth : ℕ)
    (hmesh : 0≤mesh) (hgap : mesh<ell) (ha : ell<a) (hloss : 0<loss) :
    ∀ᶠZ : ℝ in atTop,
      FixedCellPoolData (CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^a))
        Z a ell mesh loss BD Bsource depth := by
  have hell : 0<ell := hmesh.trans_lt hgap
  have ha0 : 0<a := hell.trans ha
  have hahalf : 0<a/2 := by positivity
  filter_upwards [eventually_actual_pool_card rayM H hH Sbad a loss ha0 hloss,
    eventually_actual_pool_card rayM H hH Sbad a (a/2) ha0 hahalf,
    (tendsto_rpow_atTop hahalf).eventually (eventually_ge_atTop (2*(Bsource/ell))),
    (tendsto_rpow_atTop hahalf).eventually (eventually_ge_atTop (2*(BD/ell+(depth:ℝ)+1))),
    (tendsto_rpow_atTop hell).eventually (eventually_ge_atTop (16:ℝ)),
    eventually_annular_lower a ell ha,eventually_scale_gap 2 mesh ell hgap]
    with Z hcard haux hsource hnewton hsixteen hlower hslots
  have hz : 0<Z := zero_lt_one.trans hlower.1
  let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^a)
  have haux' : Z^(a/2)≤(P.card:ℝ) := by
    simpa only [show a-a/2=a/2 by ring] using haux
  have hnorm (Q : Ideal O) (hQ : Q∈P) :
      Z^ell≤(Q.absNorm:ℝ) ∧ (Q.absNorm:ℝ)≤Z^a := by
    have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
      (Real.rpow_pos_of_pos hz a) (Finset.mem_sdiff.mp hQ).1
    exact ⟨hlower.2.trans hn.1.le,by simpa only [mul_one] using hn.2⟩
  refine ⟨hlower.1,?_,hcard,hsource.trans haux',hnewton.trans haux',
    (fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).1),
    (fun Q hQ=>(primePool_data rayM H Sbad hbad _ _ _ Q hQ).2),
    (fun Q hQ=>hsixteen.trans (hnorm Q hQ).1),
    (fun Q hQ=>(hnorm Q hQ).1),(fun Q hQ=>(hnorm Q hQ).2),hslots.2,?_⟩
  · apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (a-loss)).trans_le hcard
  · exact reciprocal_pool_bound rayM H Sbad a loss Z hz hcard

variable {P : Finset (Ideal O)} {Z a ell mesh loss BD Bsource : ℝ} {depth : ℕ}

/-- The geometric support statement applies to any prime, before specifying
slot indices, coefficients, profiles, characters or a finite slot family. -/
theorem FixedCellPoolData.not_dvd_of_norm_le
    (h : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (Q : Ideal O) (hQ : Q∈P) (w : ℝ) (hw : w≤mesh)
    (I : Ideal O) (hI : Prime I) (hN : (I.absNorm:ℝ)≤2*Z^w) : ¬Q∣I := by
  apply amplifier_not_dvd_slot Q I (h.prime Q hQ) hI Z ell mesh 2 h.marked_gap
    (h.norm_lower Q hQ)
  exact hN.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le h.scale_gt_one.le hw) (by norm_num))

/-- Full canonical prime pools are avoided, including entries whose smooth
coefficient vanishes. Zero slot width is allowed. -/
theorem FixedCellPoolData.avoids_canonical_slot
    (h : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (slotM : Ideal O) (slotH : Subgroup (O⧸slotM)ˣ)
    (w : ℝ) (hw : w≤mesh) (Q : Ideal O) (hQ : Q∈P)
    (I : Ideal O) (hI : I∈CenteredMomentPrimeSlot.primePool slotM slotH 2 (Z^w)) : ¬Q∣I := by
  exact h.not_dvd_of_norm_le Q hQ w hw I (Finset.mem_filter.mp hI).2.1
    (Collision.primePool_norm_le slotM slotH (Z^w)
      (Real.rpow_nonneg (zero_lt_one.trans h.scale_gt_one).le _) I hI).2

/-- Descendant/singleton slot subsets inherit the same original avoidance;
the scale threshold does not depend on their index type or cardinality. -/
theorem FixedCellPoolData.avoids_slot_subsets {ι : Type*}
    (h : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (slotM : Ideal O) (slotH : Subgroup (O⧸slotM)ˣ)
    (w : ι→ℝ) (S : ι→Finset (Ideal O)) (hw : ∀i,w i≤mesh)
    (hS : ∀i,S i⊆CenteredMomentPrimeSlot.primePool slotM slotH 2 (Z^(w i))) :
    ∀Q∈P,∀i,∀I∈S i,¬Q∣I := by
  intro Q hQ i I hI
  exact h.avoids_canonical_slot slotM slotH (w i) (hw i) Q hQ I (hS i hI)

/-- The same full-pool avoidance survives a finite marked product. -/
theorem FixedCellPoolData.not_dvd_marked_product {ι : Type*}
    (h : FixedCellPoolData P Z a ell mesh loss BD Bsource depth)
    (slotM : Ideal O) (slotH : Subgroup (O⧸slotM)ˣ)
    (T : Finset ι) (w : ι→ℝ) (v : ι→Ideal O)
    (hw : ∀i∈T,w i≤mesh)
    (hv : ∀i∈T,v i∈CenteredMomentPrimeSlot.primePool slotM slotH 2 (Z^(w i))) :
    ∀Q∈P,¬Q∣∏i∈T,v i := by
  intro Q hQ
  apply (h.prime Q hQ).not_dvd_finsetProd
  intro i hi
  exact h.avoids_canonical_slot slotM slotH (w i) (hw i hi) Q hQ (v i) (hv i hi)

end
end QRH.Record1252270103Source.Pool

#print axioms QRH.Record1252270103Source.Pool.eventually_annular_lower
#print axioms QRH.Record1252270103Source.Pool.eventually_fixed_cell_pool
#print axioms QRH.Record1252270103Source.Pool.FixedCellPoolData.not_dvd_of_norm_le
#print axioms QRH.Record1252270103Source.Pool.FixedCellPoolData.avoids_canonical_slot
#print axioms QRH.Record1252270103Source.Pool.FixedCellPoolData.avoids_slot_subsets
#print axioms QRH.Record1252270103Source.Pool.FixedCellPoolData.not_dvd_marked_product
