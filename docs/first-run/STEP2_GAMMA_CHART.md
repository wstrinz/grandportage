# STEP 2 — the γ-chart law at (5,20), and (a5) derived from it

**Status:** derived and machine-checked for γ ∈ {2,3}; the γ=4 chart **exists**
and is derived; its window cap is a **located obligation**, not a number.

Artifacts: `gamma_chart.py` (30/30 published data points, exits non-zero on
failure). Graph: models `GCHART_G3`, `GCHART_G2`, `GCHART_G4`,
`GCHART_G4_LEDGER`, `G3_ELIM_KILL`, `G3_ELIM_NO_A5`.

`math-stuff/` was read only. Nothing was written to it.

---

## 1. The brief, and what changed about it

> Derive **(a5)** `deg_y(C_{−k}) ≤ k+2` from the γ-chart map — `x ↦ xy³,
> y ↦ y⁻²` for γ=3; `x ↦ xy², y ↦ y⁻³` for γ=2 — acting on the reduced
> polygons `polygon_reduction.case_f2(0)` derives. **Build it for γ ∈ {2,3,4}.**
> There is no published chart map for γ=4; deriving one, or establishing that
> none exists, is part of the work.

Two of those charts were data. They are now the γ=3 and γ=2 members of a
**one-parameter family**, and the family has a fourth member.

## 2. The chart family

φ_γ(x) = x y^γ, φ_γ(y) = y^{−δ}, acting on exponents by

    (i, j)  ↦  (I, J) = (i, γi − δj)          — the x-exponent is preserved

with

    γ + δ = D := deg(P₁)/m = deg(Q₁)/n = 10/2 = 15/3 = 5,     gcd(γ, δ) = 1.

**Why γ + δ = 5.** (a1)/(b1) demand `P = C²` with `C` monic in `x`, so the
highest-x term of `P` must be a *pure power of x* downstairs: the apex `(i*,j*)`
of `N(P₁)` satisfies `γi* = δj*`, hence `(i*,j*) = s·(δ,γ)` with `gcd(γ,δ)=1`.
With `N(P₁) = m·Δ′` the apex of `Δ′` is `(δ,γ)` and `s = m`. GGV3's
`deg(P₁) = 10 = m·D` puts that apex on the total-degree face, so `δ + γ = D = 5`.

γ=5 fails `gcd`, so **γ ∈ {1,2,3,4}**:

| γ | δ | chart | det | published? |
|---|---|---|---|---|
| 1 | 4 | `x↦xy, y↦y⁻⁴` | −4 | no — excluded by GGV1 cond. (8) |
| 2 | 3 | `x↦xy², y↦y⁻³` | −3 | **yes**, GGV3 (b1)–(b6) |
| 3 | 2 | `x↦xy³, y↦y⁻²` | −2 | **yes**, GGV3 (a1)–(a6) |
| 4 | 1 | `x↦xy⁴, y↦y⁻¹` | **−1** | **no — this is the third chart** |

## 3. Four laws, 30/30 against GGV3

**L1 — bracket.** `Jac(φ_γ) = −δ·y^{γ−δ−1}`, so

    [P,Q] = −δ · x^κ · y^{κγ+γ−δ−1} = −δ · x² · y^{4γ−6}          (κ = 2)

γ=3 → `y⁶`, matching (a2). γ=2 → `y²`, matching (b2). **Two published integers
from one determinant.** γ=4 → `y¹⁰`.

**L2 — congruence.** `det(φ_γ) = −δ`, so for δ>1 **φ_γ is not an
automorphism** — GGV3's word at tex:1735 — but an injective endomorphism, a
δ-fold cover. Its image lies in `{J ≡ γI (mod δ)}`. This accounts for every
exponent pattern GGV3 states without explanation:

- (a6) `C_0` has only **even** y-exponents; (a3) `F_{−1}=y⁷` only odd — `mod 2`.
- (b5) `C_{−1}`: `1, −2, −5, …, −20`; (b6) `C_1`: `−1, −4, −7, −10` — `J ≡ 2I (mod 3)`.

**γ=4 has δ=1: no congruence at all.** The γ=4 ledger is strictly denser than
γ=2 or γ=3, and any argument leaning on a congruence there has nothing to lean
on. γ=4 is also the *only* genuine automorphism in the family.

**L3 — depression.** The second map `x ↦ x−G`, `G ∈ K[y,y⁻¹]`, is the
depressing shift: it removes `C_{δ−1}`. γ=3 removes `C_1` — (a4) has no `C_1 x`
term. γ=2 removes `C_2` — (b4) has none. γ=4 removes `C_0`.

**L4 — depth floor.** `deg(P₁) = m·D` transports to `J ≥ D(I − δ)`:

| chart | slot | predicted floor | published |
|---|---|---|---|
| γ=3 | `C_0` | −10 | (a6) `c_{0,−10}` ✓ |
| γ=2 | `C_1` | −10 | (b6) `e_{−10}` ✓ |
| γ=2 | `C_{−1}` | −20 | (b5) `c_{−1,−20}` ✓ |

The floor's normal downstairs is `(D,−1) = (5,−1) = (ρ,σ)`, GGV1's own
direction at this corner.

**L5 — the degree cap, i.e. (a5).** The complementary face gives

    J ≤ α(δ − I),   i.e.   deg_y(C_{−k}) ≤ α(k + δ).

At γ=3, `α = 1` and this **is (a5)**: `deg_y(C_{−k}) ≤ k + 2`. It is *tight on
all five* published tops — (a6) `c_{0,2}`, `C_{−1}=ay³`, `C_{−2}=by⁴`,
(a3) `F_{−1}=y⁷`, `F_{−2}` top `f₈y⁸`. At γ=2, `α = 1/4`, giving
`deg_y(C_{−k}) ≤ (k+3)/4`, tight at (b4)'s `x³`, (b5)'s `c_{−1,1}` and (b3)'s
`F_{−3}=y³`.

## 4. (a5) is load-bearing, and that is checked

GGV3 tex:1866: *"using that y⁷+3C_{−1}C_{−2}=0 and that by (a5)
deg_y(C_{−1})≤3 and deg_y(C_{−2})≤4, we get C_{−1}=ay³ and C_{−2}=by⁴."*
Since `y⁷` is a monomial and the units of `K[y,y⁻¹]` are the monomials, each
factor is a monomial `y^p, y^q` with `p+q=7`, `p≤3`, `q≤4` — and `3+4=7`
saturates the cap, so `p=3, q=4` with `a,b ∈ K^×`.

Eliminating `C_{−3}..C_{−7}` (GGV3 tex:1871) and instantiating gives 13
coefficient equations. Two runs of `cas_ideal_is_unit` (Singular, char 0):

| model | generators | result |
|---|---|---|
| `G3_ELIM_KILL` | 13 + `1−z·c_{0,−10}` + `1−w·a` | `std(I) = 1` → **EMPTY** |
| `G3_ELIM_NO_A5` | same, `1−w·a` **removed** | `std(I) ≠ 1` → **NONEMPTY** |

The second is a negative control: withhold only what (a5) buys — that `a` is a
*unit* — and the contradiction no longer closes. Explicit point:
`a=b=λ=f₂=f₄=f₆=f₈=0`, `c_{0,j}=0` for `j>−10`, `c_{0,−10}=1`; at `a=0` the
quadratic term drops and the identity degenerates to `S·T = 0`.

So **(a5) is a hypothesis the (50,75) γ=3 kill actually stands on**, and
deriving it derives a load-bearing step. The kill is recorded as
`GC-G3-KILL` (EMPTY, `UNIT_IDEAL_CERT`, scope SCHEME) and transported
**AGAINST** the elimination edge and **AGAINST** `GE7` to `REDUCED_5_20`
(`GI-G3-KILL-LIFTS`, clean). Reading the elimination the other way round —
"I eliminated and got a contradiction, so it propagates forward" — is
`IMAGE_CLOSURE`/ALONG/EMPTY, which is **NO**.

Nothing here transports to (75,125). That is `GE4`, still `UNTYPED`.

## 5. γ = 4 — the third chart exists

**The obligation from Step 1 was: exclude γ=4 at (5,20), or a third chart
exists that GGV3 §5 does not analyse.** The second disjunct holds.

    φ₄ :  x ↦ x y⁴,   y ↦ y⁻¹

- `det = −1`: the **only** member of the family that is a true automorphism.
- `[P,Q] = −x²y¹⁰(x−G)²`.
- **no support congruence** (δ=1).
- `C = x + C_{−1}x⁻¹ + ⋯`, `deg_x C = 1`; the shift removes `C_0`.
- depth floor `J ≥ 5(I−1)`: `C_0 ≥ −5`, `C_{−1} ≥ −10`, `C_{−2} ≥ −15`.

## 6. What is NOT derived, and exactly where it lives

**The γ=4 cap slope α.** Recorded as `GE10`, `UNTYPED`, with `debt_why`.

α is the slope of the face of `N(P₁)` *complementary* to the total-degree face.
The total-degree face is chart-independent — which is why L4 works for every γ.
The complementary face is not: it is fixed by `Δ′_γ`, and `Δ′_4` is unknown.
Two values, α=1 at γ=3 and α=1/4 at γ=2, do not determine a third. `α = 4^{3−γ}`
fits both; so do infinitely many others. Fitting one and calling it a
derivation is the failure mode this whole exercise exists to avoid, so
`GI-G4-CAP-EXTRAPOLATION` is recorded as a **type error**, in the baseline
alongside `GI-GAMMA-IMPORT`.

**Where `Δ′_4` lives — and this is the useful part.**

`polygon_reduction.case_f2(0)` computes `Δ′ = {(0,0),(3,0),(4,1),(0,5)}`. Its
max-x vertex is `(4,1) = (δ,γ)` **with γ = 1**, on the total-degree face. So
`Δ′` is the **γ=1 member of the family** — and γ=1 is excluded by GGV1
condition (8) (`gamma_from_corner.py`: `A⁽¹⁾ = (6/5,1)` gives `ρ−a′/b′ = −1`
and `gcd(6,1)=1`).

`Δ′` still reproduces all three integers GGV3 publishes — `[P₁,Q₁]=x²`,
`deg P₁=10`, `deg Q₁=15` — because **none of them sees `deg_x`**. GGV3's γ=3
chart needs `deg_x(P₁)=4` and γ=2 needs `6`; `Δ′` gives `8`.

The structural reason. The pre-inversion upper edge runs `(0,1)—(20,5)` and
carries the lattice points `(5t, 1+t)`, `t = 0..4`. The inversion
`(i,j) ↦ (4j−i, j)` sends them to `(4−t, 1+t) = (δ,γ)` for `γ = t+1`:

    t=0 → (4,1) γ=1     t=1 → (3,2) γ=2     t=2 → (2,3) γ=3
    t=3 → (1,4) γ=4     t=4 → (0,5) γ=5

**`t` is the edge-root-shift depth** — GGHV22's `φ₃` step, which
`case_8_28()` performs (`t=6`, `(0,1) → (24,7)`) and which `case_f2()` does
not. `case_f2`'s five-branch manifest has no branch for it.

**So γ *is* the edge-root-shift depth, and the branch `case_f2` omits is
exactly where γ lives.** That is a one-function, locatable repair, and it is
what closes the γ=4 cap.

## 7. Next

1. Add the edge-root-shift branch to `polygon_reduction.case_f2` (t = 0..4,
   each tagged FOLLOWED/EXCLUDED), giving `Δ′_γ` and hence α for every γ.
2. With α₄ in hand, build the γ=4 window system and run the same two
   `cas_ideal_is_unit` calls. Either γ=4 is killed at (50,75) — which would
   *discharge* `GI-GAMMA-IMPORT`, not merely record it — or it survives, and
   GGV3 §5's case analysis is incomplete.
3. Only then does (75,125) become approachable; `GE4` stays `UNTYPED` until the
   compiler derives that system rather than replaying this one.
