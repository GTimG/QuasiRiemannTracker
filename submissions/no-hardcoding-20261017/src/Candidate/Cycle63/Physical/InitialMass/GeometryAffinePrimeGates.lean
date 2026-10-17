/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorCoprime
import Candidate.Cycle63.Arithmetic.LocalReserves
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeElements

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary
open CenteredMomentAmplificationSlotGap CenteredMomentPrimeElements
open ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance affinePrimeGatesFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- One threshold separates every amplifier cell from all stored slots.
It does not discard entries whose smooth profile happens to vanish. -/
theorem eventual_geometry_affine_prime_coprime
    (S : Finset (Ideal O)) (hS : fixedBadPrimes⊆S) (b mesh : ℝ)
    (hmesh : mesh<Cycle63.Arithmetic.amplifierFloor/2) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀beta : ℝ,Cycle63.Optimization.firstCellTop≤beta → beta≤Cycle63.Optimization.slotTop →
      let P:=CenteredMomentPrimePool.primePool M H S (1/2) 1
        (Z^(Cycle63.Arithmetic.amp beta))
      ∀{α : Type*}[Fintype α][DecidableEq α]
        (s : Input α)(η₀ : Character)(θ : α→RayQuotient.Characters M H)
        (w σ v : α→ℝ)(W : ℝ→ℂ),
        Matches M H hH s η₀ θ w σ v W b Z → (∀i,w i≤mesh) →
        ∀q : elementPool P,∀i I,I∈s.slots i→IsCoprime (Ideal.span {q.val}) I := by
  let ell : ℝ:=Cycle63.Arithmetic.amplifierFloor/2
  have hell : 0<ell := by
    have := Cycle63.Arithmetic.amplifierFloor_pos
    dsimp only [ell]
    positivity
  filter_upwards [eventually_scale_gap (max 1 b) mesh ell hmesh,
    (tendsto_rpow_atTop hell).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hgap hlarge hZ
  refine ⟨hZ,?_⟩
  intro beta hlo hhi P α _ _ s η₀ θ w σ v W hm hw q i I hI
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hp : ∀Q∈P,Prime Q:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).1
  have hbad : ∀Q∈P,Q∉fixedBadPrimes:=fun Q hQ=>(primePool_data M H S hS _ _ _ Q hQ).2
  have hq:=elementPool_data P hp hbad q.val q.property
  have hn:=PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz _) (Finset.mem_sdiff.mp hq.2.1).1
  have hlow : Z^ell≤(1/2:ℝ)*Z^(Cycle63.Arithmetic.amp beta) := by
    have ha : ell+ell≤Cycle63.Arithmetic.amp beta := by
      have h:=(Cycle63.Arithmetic.amp_bounds ⟨hlo,hhi⟩).1
      dsimp only [ell]
      linarith
    have hr:=Real.rpow_le_rpow_of_exponent_le hZ.le ha
    rw [Real.rpow_add hz] at hr
    have hnonneg:=Real.rpow_nonneg hz.le ell
    have hx : 2 * Z^ell ≤ Z^(Cycle63.Arithmetic.amp beta) :=
      (mul_le_mul_of_nonneg_right hlarge hnonneg).trans hr
    calc
      Z^ell = (1/2:ℝ) * (2 * Z^ell) := by ring
      _ ≤ (1/2:ℝ) * Z^(Cycle63.Arithmetic.amp beta) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
  exact actual_full_slot_coprime M H hH s η₀ θ w σ v W b Z mesh ell hZ.le hm hw
    (Ideal.span {q.val}) (hp _ hq.2.1)
    (hlow.trans (by simpa only [mul_comm] using hn.1.le)) hgap.2 i I hI

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_geometry_affine_prime_coprime
