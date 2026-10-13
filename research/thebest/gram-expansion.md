# Exact mixed Gram expansion and the sixth-power diagonal

Research note, 2026-10-13. This note proves finite identities and an upper
bound for their arithmetic diagonal. It does **not** prove the required
mixed moment or improve the zero-free boundary. The starting point is
[Cycle25, B0.2–B0.5, B0.38–B0.44 and B1.1](../../../proofs/cycle25-quartic-20261010/manuscript/paper.tex),
with notation and proposed interfaces from [joint-moment.md](joint-moment.md).
No claim of being the first joint-moment approach is made; other research
submissions can use joint moments with different reconstructed variables.
The particular object here is the tensor product of the actual zero witness,
reflected physical numerator, and selected prime marks.

## 1. Finite setup, with the actual row zeros

Work with good ideals in the Eisenstein integers, represented by the
manuscript's canonical generators. Put `q_a = Na` and
`psi_u(a) = chi_a(u)`. Every character power is extended by zero at
nonunits, including its zeroth and sixth powers. Let `B` be any finite set
of element rows, including their units, and `w(u) >= 0` any row weights.
The buffered zero bin intersected with natural eligible rows is an allowed
choice. Set `W_B = sum_B w(u)`.

For finitely supported, row-independent coefficients, define

\[
 F_j(u)=\sum_a b_j(a)\psi_u(a)^{\epsilon_j},\qquad
 \epsilon_j\in\{+1,-1\},\qquad F(u)=\prod_{j=1}^kF_j(u).
\]

Here the exponent `-1` means conjugation on units and zero on nonunits;
it is not division by a zero character value. Fixed ray characters,
Möbius factors, normalized annular weights, and independent heights all
belong in `b_j`. No row-dependent physical Euler coefficients are hidden
in this notation.

For a tuple `tau=(a_1,...,a_k)`, set

\[
 c_\tau=\prod_j b_j(a_j),\quad
 R_\tau=\operatorname{rad}\!\left(\prod_j a_j\right),\quad
 v_{\tau,\mathfrak p}=\sum_j\epsilon_j
      \operatorname{ord}_{\mathfrak p}(a_j)\pmod6.
\]

Only finitely many coordinates of `v_tau` are nonzero. Define the tuple
character explicitly by

\[
 T_\tau(u)=\mathbf1_{(u,R_\tau)=1}
       \prod_{\mathfrak p\mid R_\tau}
       \chi_{\mathfrak p}(u)^{v_{\tau,\mathfrak p}},
\]

where the factors in the product are evaluated only on units. Finite
distributivity and denominator multiplicativity give the exact identity

\[
 \boxed{\quad
 \sum_{u\in B}w(u)|F(u)|^2
 =\sum_{\tau,\tau'}c_\tau\overline{c_{\tau'}}K_B(\tau,\tau'),
 \quad}
 \tag{G1}
\]

with

\[
 K_B(\tau,\tau')=
 \sum_{u\in B}w(u)\mathbf1_{(u,R_\tau R_{\tau'})=1}
 \prod_{\mathfrak p\mid R_\tau R_{\tau'}}
 \chi_{\mathfrak p}(u)^{v_{\tau,\mathfrak p}-v_{\tau',\mathfrak p}}.
 \tag{G2}
\]

The matrix is Hermitian positive semidefinite: its quadratic form is a
sum of squares with weights `w(u)`. This proves (G1) without reciprocity,
Poisson summation, zero-free assumptions, or an asymptotic estimate.

**A necessary distinction.** Reducing exponents modulo six does not
remove the support radical. For example, `a=p^6` and `a'=1` have the same
residual vector, but their Gram entry is
`sum_B w(u) 1_(p,u)=1`, not `W_B`. The exact feature key is the pair
`(R_tau,v_tau)`. A rational signed product is a convenient shorthand only
if this additional support datum is retained.

## 2. The three proposed interfaces are instances of one identity

Write `A=S_num(U^n)` for one common reflected annular numerator profile,
`M_r=M(U^r)`, `S_m=S_det(U^m)`, and `Q=prod_i Q_i` for the selected marks.
Then the quantities proposed in the companion note are

| Interface | Polynomial `F` in (G1) | Factor normalization | Product norm scale |
| --- | --- | --- | --- |
| `J_I` | `M_r A Q` | `U^(-(r+n+z)/2)` | `X=U^(r+n+z)` |
| `J_P` | `S_m S_m A Q` | `U^(-(2m+n+z)/2)` | `X=U^(2m+n+z)` |
| `J_L` | `M_r A` | `U^(-(r+n)/2)` | `X=U^(r+n)` |

Here `z=sum_i z_i`; each individual mark is one prime-supported factor.
These are literal product norm scales, **not** the moment-capacity
expressions `r+n+2z` and `2m+n+6 kappa z`. Capacity prices from existing
estimates cannot be inferred from polynomial support length alone.

For `J_I`, for example, a tuple coefficient is exactly

\[
 U^{-(r+n+z)/2}\mu(a)\nu_I(a)\nu_A(b)
 W_I(q_a/U^r)W_A(q_b/U^n)
 \prod_i a_i(p_i)\nu_i(p_i)W_i(q_{p_i}/U^{z_i}),
\]

with its own height twists in each factor. It is not the Möbius
coefficient of the product ideal. Consequently (G1) does not authorize
applying MI to that convolution. Likewise `S_m^2 A` is not the single
plain polynomial required by MP.

For estimating the absolute mixed moment, there is a useful simplification:
**conjugate each entire negatively oriented factor separately.** Its
absolute value is unchanged, while its fixed coefficient becomes
`conj(b_j)` and its orientation becomes positive. Thus all factors may
be aligned for (G1). This operation conjugates their fixed twists and
profiles and reverses their heights; it imposes no common-height
condition. The signed version (G2) remains useful if cross terms between
different physical profiles must be preserved.

## 3. A proved diagonal bound: no diagonal power-loss obstruction

Assume each of the fixed number `k` of aligned factors is supported on
`q_a <= C_j L_j`, and

\[
 |b_j(a)|\le C_j L_j^{-1/2},\qquad L_j\ge1.
 \tag{G3}
\]

Annular profiles have this property after recording their fixed
seminorms and height costs. Prime supports only restrict the sums, and
`|mu|<=1`. Let `X=prod_j L_j`. Grouping by the actual product ideal gives

\[
 F(u)=\sum_n C(n)\psi_u(n),\qquad
 C(n)=\sum_{a_1\cdots a_k=n}\prod_j b_j(a_j).
 \tag{G4}
\]

For each `epsilon>0`, the ideal divisor bound implies

\[
 \operatorname{supp}C\subset\{q_n\le CX\},\qquad
 |C(n)|\ll_{k,\epsilon,C_j}X^{-1/2+\epsilon}.
 \tag{G5}
\]

Define the **sixth-power diagonal** `D_B` to be the contribution from
pairs `(n,n')` whose prime valuations agree modulo six. Equivalently,
write uniquely `n=d a^6`, `n'=d b^6`, with `d` sixth-power-free. This is
larger than the equality diagonal `n=n'`. Natural row zeros remain in
its exact expression:

\[
 D_B=\sum_{d\ (6)}\sum_{u\in B}w(u)|\psi_u(d)|^2
       \left|\sum_a C(da^6)\mathbf1_{(u,a)=1}\right|^2\ge0.
 \tag{G6}
\]

**Proposition.** Under (G3), for every `epsilon>0`,

\[
 \boxed{\qquad 0\le D_B\ll W_B X^\epsilon.\qquad}
 \tag{G7}
\]

**Proof.** The number of ideals of norm at most `Y` is `O(Y)` in this
fixed number field. For a fixed `d`, the number of possible `a` is
`O((X/q_d)^(1/6))`. By (G5), after relabeling epsilon,

\[
 D_B\ll W_BX^{-1+\epsilon}
       \sum_{q_d\le CX}(X/q_d)^{1/3}
 \ll W_BX^{-1+\epsilon}X^{1/3}X^{2/3}
 =W_BX^\epsilon.
\]

Dropping the sixth-power-free restriction in this upper bound is
permissible. The second estimate follows by partial summation from the
ideal counting bound. This proof uses absolute coefficient values and
so holds uniformly over all fixed twists and independent height phases.
It does not require cancellation of Möbius coefficients. ∎

If the row norms are `O(U)`, bounded row weights give `W_B=O(U)`.
All bounded polynomial length ranges therefore have
`D_B << U^(1+epsilon)`. In particular the diagonal is compatible with
`lambda=0` for both short interfaces, and with `e(r)+lambda` for the
long interface since `e(r)>=1`. This is a concrete favorable result:
the full sixth-power diagonal does **not** force the positive excess
exponent which blocks the desired estimate. It is an upper bound, not
a prediction that the full moment has this size.

The constants depend on the fixed number of slots. This is compatible
with choosing the slot system before sending `U` to infinity, as in
Cycle25; it is not a bound with constants uniform in a growing slot count.

## 4. Exactly what remains off the diagonal

Write the full mixed moment as `D_B+O_B`, defining `O_B` by the remaining
pairs in (G1). It is real but need not be nonnegative. Thus an isolated
large diagonal would not itself lower-bound the full moment without
control of the off-diagonal. Conversely, (G7) does not upper-bound the
full moment: it leaves `O_B` completely open.

There is a useful exact reference ensemble. Let `P` be the product of
all good primes appearing in the finite factors, and average uniformly
over *all* residues `u mod P`. Character orthogonality and the Chinese
remainder theorem give

\[
 \frac1{q_P}\sum_{u\bmod P}T_\tau(u)\overline{T_{\tau'}(u)}
 =\begin{cases}
 \displaystyle\prod_{\mathfrak p\mid R_\tau R_{\tau'}}(1-q_\mathfrak p^{-1}),
       &v_\tau=v_{\tau'},\\
 0,&v_\tau\ne v_{\tau'}.
 \end{cases}
 \tag{G8}
\]

The local sextic character has exact order six at the good primes in
question. Formula (G8) supplies a finite debugging baseline, not an
orthogonality theorem on annular rows or zero-selected bins. Such bins
can correlate with the characters. Nor does their positivity allow
termwise replacement of `K_B` by the unrestricted-row kernel.

## 5. A narrower analytic target and a meaningful next experiment

The remaining task can now be stated without a heuristic independence
assumption. For the specific tensor coefficient `C` in each interface,
prove an **upper bound for its off-diagonal quadratic form**, with the
original eligible zero-bin mask, of the following sizes:

\[
 O_{I,B},O_{P,B}\le C_\epsilon U^{1+\lambda+\epsilon},\qquad
 O_{L,B}\le C_\epsilon U^{e(r)+\lambda+\epsilon},\qquad \lambda\ge0.
 \tag{G9}
\]

Together with (G7), these imply the proposed joint interfaces. An
absolute-value bound on each kernel entry is sufficient but could lose
the cancellation in `mu(a)` and the convolution; the signed quadratic
form is the actual target. At the displayed short binding cell the
companion calculation asks for `lambda < 0.196590173946`, whereas the
pointwise reduction provides `lambda = 0.197587220845`. These are local
floating-point diagnostics, not certified endpoint constants.

The finite identity suggests a sharper experiment than comparing only
raw mixed-moment sizes. On genuine Eisenstein row annuli, record three
quantities with identical profiles and row masks: the full moment,
the exact `D_B` of (G6), and their signed difference `O_B`. Also compare
`O_B` before and after replacing the inverse factor's Möbius coefficients
by their absolute values. Vary independent heights and fixed twists,
and include pairs with equal sixth-power-free core but different
radicals. This measures precisely which contribution would have to
improve. A complete-residue toy model necessarily has zero off-diagonal
and therefore cannot substantiate the missing analytic saving.

A proof through reciprocity/Poisson must keep the fixed ray phase from
B1.1 and the coprimality masks in (G2). A proof only for all unrestricted
rows would need a justified transfer to the buffered/eligible interface;
it cannot simply drop the mask inside the signed quadratic form.
Alternatively, an upper bound for the *full positive moment* on a valid
larger row set does transfer by positivity, if the requisite moment
estimate genuinely holds on that larger set.

Finally, all three branches, including the equally binding long inverse
endpoint, require estimates in a neighborhood of the binding geometry.
The reflected numerator scale depends on the row conductor and Euler
shifts. The finite identities above hold for fixed common annular
profiles; extending (G9) to the common-profile scale suprema used in
B0.44, with the stated coefficient damping and natural zeros, is a
separate required step. Multiplying by arbitrary row-dependent Euler
coefficients would invalidate (G4)'s fixed-coefficient hypothesis.

The proved advance here is the exact kernel, the correction for residual
zero exponents, and the uniform `U^(1+epsilon)` bound for its full
sixth-power diagonal at the proposed mixed lengths. Any actual gain
must now come from an arithmetic estimate of the remaining signed
quadratic forms, not from further diagonal counting or generic changes
of Hölder exponents.

## Finite algebra reproduction

Run `uv run research/thebest/gram-check.py`; the standard-library-only
checker writes [gram-check-results.json](gram-check-results.json). It
compares a direct `|M|^2 |S|^4` moment with its product and Gram expansions
using exact arithmetic in `Q(zeta_6)`, on complete and weighted incomplete
residue sets with both orientations. This 2-by-4 toy instance checks the
general algebra (G1), not specifically the marked `J_I` interface or the
asymptotic estimate (G9). It also checks (G8), the support distinction
between `1` and `7^6`, and the explicit example `1-chi_7(u)` on the single
row `u=1`, where the diagonal is `2`, off-diagonal is `-2`, and moment is
zero. The proof of (G7) above is mathematical; a finite toy calculation
cannot verify its uniform asymptotic content.
