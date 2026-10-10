import ZetaZeroFree.Analytic.Energy.Geometry
import OAI.NumberTheory.DirichletL.Reflection.NormalizedEnergy
import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
import OAI.NumberTheory.DirichletL.Reflection.LowWidth
import OAI.NumberTheory.DirichletL.Reflection.SurvivingGate
import OAI.NumberTheory.DirichletL.Reflection.RawTail
import OAI.NumberTheory.DirichletL.Reflection.RetainedCaps
import OAI.NumberTheory.DirichletL.Reflection.BranchCount
import OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
import OAI.NumberTheory.DirichletL.Reflection.CountBudget
import OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
import OAI.NumberTheory.DirichletL.Reflection.ActualSizeCaps

/-! The actual integrated reflected branch satisfies the new retained-block
bound. Finite assembly below is conditional on a proved source decomposition;
it is not the original whole-index theta-energy endpoint. -/

namespace ZetaZeroFree.Analytic.Energy
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open InverseReflectedPhase InverseReflectedNormalization InverseTerminalWidths
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss
open CanonicalQuadraticSieve InverseMoment CompletedDyadic
noncomputable section
universe v
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem actual_retained_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z O H A N₀ v ell el S₀ B₀ Td za η τ : ℝ), 1 ≤ Z →
    ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      X = Z^H → extractedDualScale (frozenExtracted F jF e 1) Y = Z^v →
      extractedDualScale (frozenExtracted F jF e 2) B = Z^ell → L = Z^za →
      ‖scalar‖*frozenBranchScale F jF e = outsideScalar Z v ell el S₀ B₀ Td →
      0 ≤ O → 0 ≤ S₀ → 0 ≤ B₀ → 0 ≤ N₀ → N₀ ≤ A → 2*A ≤ O →
      za ≤ z → 0 ≤ v → 0 ≤ ell → -η ≤ el → 0 ≤ η → 0 ≤ τ →
      H ≤ M-O+η → Td = dualLength H A za N₀ B₀ →
      v+3*ell+el ≤ Td+τ →
      Z^(O/2) * (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      (6*C)*Z^(M + 4*η + τ + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := normalized_actual_reflected_branch_energy
    (Ω := Ω) (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro Z O H A N₀ v ell el S₀ B₀ Td za η τ hZ X Y B L hX hY hB hL
    F jF e s hc hN hbase hac hF hNF hcharF hj ι _ G0 D0 u m rows nset bset Pset S
    μ density scalar r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP
    hdensity hrM hawM hwM hr haw hw hscaleX hscaleY hscaleB hscaleL hscalar
    hO hS hB₀ hN₀ hNA hA hza hv hell hel hη hτ hH hTd hret
  have hh := he Z H v ell el S₀ B₀ Td za hZ X Y B L hX hY hB hL
    F jF e s hc hN hbase hac hF hNF hcharF hj G0 D0 u m rows nset bset Pset S
    μ density scalar r aw w hrows hrowcop hproducts hScop hSN hSchar hn hb hP
    hdensity hrM hawM hwM hr haw hw hscaleX hscaleY hscaleB hscaleL hscalar
  have hg := retained_block_bound_buffered hO hS hB₀ hN₀ hNA hA hza hv hell hel hη hτ hH
    (by simpa only [hTd] using hret)
  have hex : O/2 + InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td ≤ M+4*η+τ := by
    rw [hTd]
    unfold InverseTerminalWidths.reflectedExponent at hg ⊢
    linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    _ ≤ Z^(O/2) * ((6*C)*Z^(InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hZ0.le _)
    _ = (6*C)*Z^(O/2 + InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2 := by
      calc
        _ = (6*C)*(Z^(O/2)*Z^(InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za))) *
            (∫ t, ‖density t‖ ∂μ)^2 := by ring
        _ = _ := by
          simp only [Real.rpow_add hZ0]
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)) (sq_nonneg _)

/-- The new retained geometry applies to actual surviving dyads of original
rows; the input is a physical row norm bound, not an energy estimate. -/
theorem original_surviving_retained_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (kK kP η : ℝ) (hkK : 0 < kK) (hkP : 0 < kP) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧
    ∀ (J I F Q Q₀ : Ideal Eis), J ≠ 0 → I ≠ 0 → Q ≠ 0 →
      rowPowerfulPart J = rowPowerfulPart I → rowMaskPart J Q = rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀)) (e : A → Fin 3)
      (column : Ideal Eis → Ideal Eis → ℂ)
      (Z O H za Ns shift δ Ck CO CH X QK QP : ℝ) (i : ℕ × ℕ × ℕ),
      Z₀ ≤ Z → 0 < Ck → 0 < CO → 0 < CH → 0 < X → 0 < QK → 0 < QP →
      (Ideal.absNorm I : ℝ) ≤ Ck * Z^M →
      Z^O/CO ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) →
      Z^H/CH ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z ≤ η →
      normWidth Z (rowPowerfulPart I) ≤ O+η → normWidth Z Q ≤ η →
      0 ≤ O → za ≤ z+η → |shift| ≤ η → 0 ≤ δ →
      Ns = Nstar+shift → H = Real.logb Z (kK*QK) →
      za = Real.logb Z (kP*QP) → Ns = Real.logb Z X →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      i ∈ retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e ∈ survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let b := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent O H
        (normWidth Z (frozenExtracted G j e 0)) (normWidth Z (frozenExtracted G j e 2))
        za v b (ramifiedWidth Z i.1) (terminalDualWidth Z H za Ns G.ideal j e) ≤
      M+13*η+δ := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc kK kP η hkK hkP hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O H za Ns shift δ Ck CO CH X QK QP i hZ hCk hCO hCH hX hQK hQP
    hIn hPow hRow hlog hPowUpper hQwidth hO hza hshift hδ hNs heH heza heN
  dsimp only
  intro hret hsurv
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1 < Z := hZ₀.trans_le hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨hv,hb,hel,hwidth⟩ := hgates G hpair j column e Z X QK QP δ i hZ hX hQK hQP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  have hH := physical_residual_width I Q hI Z M O H Ck CO CH hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q₀ hJ hI hQ hpower hmask A Z hz
  have hN := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have hTd : terminalDualWidth Z H za Ns G.ideal j e =
      dualLength H (normWidth Z (∏ b,G.ideal b)) za
        (normWidth Z (frozenExtracted G j e 1)) (normWidth Z (frozenExtracted G j e 2)) - shift := by
    unfold terminalDualWidth dualLength
    rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal]
    ring
  have hs := abs_le.mp hshift
  have hg := retained_block_bound_with_errors (H := H)
    (Td := terminalDualWidth Z H za Ns G.ideal j e) (τ := δ+η)
    (ρ := 3*η) (σ := η) (ν := η)
    hO hS hB hN hNA (by linarith) hza hv hb hel hη.le (by linarith : 0 ≤ δ+η)
    (by linarith) hη.le hη.le (by linarith) (by rw [hTd]; linarith)
    (by rw [hTd]; linarith) (by linarith)
  dsimp only [G,j] at hg
  linarith

/-- Actual surviving branch aggregation at the new row scale. -/
theorem original_surviving_retained_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Ns shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Ns=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Ns G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(M+13*η+δ+π-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_retained_exponent s hc kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column
    Z O₀ H za Ns shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Ns shift δ Ck CO CH X QK QP i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hδ hNs heH heza heN hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(M+13*η+δ+π-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      have hbnd := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
        (kK*QK) (kP*QP) (familyRawScale_pos G s hc X QK QP hX hQK hQP) hz'
        (mul_pos hkK hQK) (mul_pos hkP hQP) hscap hconst hrowcap hslotcap i hret
        (frozenExtracted G j e 1) (frozenExtracted G j e 2)
        (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
      rw [←heH,←heza] at hbnd
      have hbnd' := mul_le_mul_of_nonneg_left hbnd hε
      unfold InverseTerminalWidths.reflectedExponent at hh ⊢
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(M+13*η+δ+π-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)

/-- Actual literal dyadic row energy in one fixed sector at M=28/33.
The powerful-row count remains outside this residual-row estimate. -/
theorem original_retained_sector_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Ns=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc),
      (∀ f,IsCoprime (Ideal.span {N}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(M+13*η+δ+π-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=N) ε hε lo hi hlo W hWs hW s hc η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_retained_energy_sum s hc ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hN hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F Q Q₀ hJ hI hQ hpower hmask A (actualCuspColumn E.referenceArithmetic s hc u i.1)
    Z O₀ H za Ns shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift hNs
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hδ hδη hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Ns G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(M+13*η+δ+π-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(M+13*η+δ+π-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith

theorem original_retained_sector_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Ns=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc),
      (∀ f,IsCoprime (Ideal.span {N}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(M+13*η+δ+π-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_retained_sector_literal_energy
    (N:=N) ε hε lo hi hlo W hWs hW s hc hN hbase hac ρ hρ η hηpos
  refine ⟨degree,36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F Q Q₀ hJ hI hQ hpower hmask A
      Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
      hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring

theorem original_retained_sector_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Ns=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc),
      (∀ f,IsCoprime (Ideal.span {N}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_retained_sector_energy
    (N:=N) ε hε lo hi hlo W hWs hW s hc hN hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift δ π Ck CO CH X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(M+13*η+δ+π-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(M+13*η+δ+π-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith)) (by positivity)

theorem original_sector_whole_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Ns=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc),
      (∀ f,IsCoprime (Ideal.span {N}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_retained_sector_budget
    (N:=N) ε hε lo hi hlo W hWs hW s hc hN hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc hN hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by positivity
      nlinarith only [hp]

theorem original_sector_whole_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤O₀ → za≤z+η → |shift|≤η →
      Ns=Nstar+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Ns=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤M+13*η+δ+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) G rows Pset S hrows s hc),
      (∀ f,IsCoprime (Ideal.span {N}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {N}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_sector_whole_energy
    (N:=N) Adecay ε hε lo hi hlo W hWs hW s hc hN hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Ns shift π Ck CO CH X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(M+13*η+δ+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith only [hp]

/-- Actual reflected lattice tails beat any fixed polynomial coefficient and
scale cost. This uses the proved raw-kernel summability bound behind B.25. -/
theorem raw_tail_arbitrary_power (lo hi δ R L : ℝ) (hlo : 0 < lo) (hδ : 0 < δ) :
    ∃ (orders : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc lo hi →
    ∀ (Z scale : ℝ), 1 ≤ Z → 0 < scale → (scale^2)⁻¹ ≤ Z^L →
    ∀ (β : ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ m, ∀ I J : NonzeroDualIdeal, ‖β m I.val J.val‖ ≤ Z^L) →
    ∀ (cut : RawTailIndex → Prop),
      (∀ x, cut x → Z^δ ≤ scale*(completedRamifiedStep^x.1)^3*
        (Ideal.absNorm x.2.1.val : ℝ)*(Ideal.absNorm x.2.2.val : ℝ)^3) →
      Summable (fun x => ‖if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep β x else 0‖) ∧
      ‖∑' x, if cut x then rawDualKernelTerm V scale 1 completedRamifiedStep β x else 0‖ ≤
        C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * Z^(-R) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((2*L+R)/δ)
  have hsave : 2*L - δ*(A:ℝ) ≤ -R := by
    have hh := (div_lt_iff₀ hδ).mp hA
    linarith
  obtain ⟨orders,C,hC,hbound⟩ := raw_kernel_tail lo hi completedRamifiedStep
    hlo completedRamifiedStep_gt_one A
  refine ⟨orders,C,hC,?_⟩
  intro V hV Z scale hZ hs hscale β hβ cut hcut
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hh := hbound V hV scale 1 (Z^L) (Z^δ) hs (by norm_num)
    (Real.rpow_nonneg hz.le _) (Real.rpow_pos_of_pos hz _) β hβ cut
    (by simpa only [one_mul] using hcut)
  refine ⟨hh.1,hh.2.trans ?_⟩
  simp only [one_pow,mul_one] at *
  have hdecay : (Z^δ)^(-(A:ℝ)) = Z^(-δ*(A:ℝ)) := by
    rw [← Real.rpow_mul hz.le]
    congr 1
    ring
  calc
    _ ≤ C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * Z^L *
        (Z^δ)^(-(A:ℝ)) * Z^L :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * Z^(2*L-δ*(A:ℝ)) := by
      rw [hdecay]
      calc
        _ = (C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (Z^L * Z^(-δ*(A:ℝ)) * Z^L) := by ring
        _ = _ := by
          rw [← Real.rpow_add hz,← Real.rpow_add hz]
          congr 2
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsave) (by positivity)

/-- This is a conversion from individually proved branch bounds and an exact
finite source identity. The theta-source identity is a separate obligation. -/
theorem finite_assembly_of_source_identity {ι κ : Type*}
    (blocks : Finset ι) (rows : Finset κ) (w : ι → ℂ)
    (f : ι → κ → ℂ) (source : κ → ℂ) (Z C ε : ℝ)
    (hsource : ∀ k ∈ rows, source k = ∑ i ∈ blocks, w i * f i k)
    (hbranch : ∀ i ∈ blocks, (∑ k ∈ rows, ‖f i k‖^2) ≤ C * Z^(M+ε)) :
    (∑ k ∈ rows, ‖source k‖^2) ≤
      (∑ i ∈ blocks, ‖w i‖)^2 * C * Z^(M+ε) := by
  have hh := weighted_finite_row_energy_uniform blocks rows w f (C * Z^(M+ε)) hbranch
  have hid : (∑ k ∈ rows, ‖source k‖^2) =
      ∑ k ∈ rows, ‖∑ i ∈ blocks, w i * f i k‖^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsource k hk]
  rw [hid]
  exact hh.trans_eq (by ring)

end
end ZetaZeroFree.Analytic.Energy
