# Fifteen minutes with the Fano plane

You will find the characteristic set of the Fano plane F7. Along the way you will make three classic mistakes, and GP will refuse each one.

A rank-3 matroid M is realizable in characteristic p when its points can be drawn in a projective plane over some field of characteristic p. Its *characteristic set* χ(M) is the set of characteristics where it is realizable. The textbook says χ(F7) = {2}. We will make the ledger say it.

Every command below is run as `gp …`, which stands for:

```
python tools/gp.py --campaign campaigns/3p-matroids …
```

The receipts used here are in `campaigns/3p-matroids/receipts/`. Singular produced them. GP does not trust Singular: it replays every receipt itself.

## 1. Start the ledger

```
gp init
```

F7 is listed in `campaign.json`. `--matroid F7` encodes it as a polynomial system. Each element gets a column (x, y, z), and four columns are fixed to a frame. Collinear triples give equations and non-collinear triples give guards (`nonzero`). That normalization is the premise `ENCODING-FRAME`, which stays visibly OPEN on every result.

## 2. Mistake one: "Fano is realizable nowhere"

After the frame, six equations are linear. The last one, for the line {4, 5, 7}, reduces to `2·x4·y5·z7 = 0`, and x4, y5 and z7 are guards. So there is no realization. Singular gives the identity, with cofactors that divide by 2. Claim emptiness everywhere, starting with characteristic 2:

```
gp claim F7-empty-2 --matroid F7 --kind EMPTY --char 2
gp submit F7-empty-2 receipts/F7-empty-q.json
refused: the certificate reaches 0 and every prime except {2}, which does not cover the
requested characteristic 2 [rule: receipt: computed reach; scope: characteristic 2];
smallest fix: narrow the claim to the computed reach, or certify the excluded
characteristics separately (for example mod p)
```

The identity is correct, but GP computed its **reach**: a certificate that divides by 2 says nothing where 2 = 0. Take the advice and narrow the claim:

```
gp claim F7-empty-outside2 --matroid F7 --kind EMPTY --outside 2
gp submit F7-empty-outside2 receipts/F7-empty-q.json
held: F7-empty-outside2 at characteristic 0 and every prime except [2]
```

## 3. Mistake two: a floating-point realization

A numerical search "finds" F7 over ℚ, with y5 = z5 = 0.000000001. GP will not read decimals at all. Write them as exact fractions (1/1000000000) and replay:

```
gp claim F7-nonempty-q --matroid F7 --kind NONEMPTY --char0
gp submit F7-nonempty-q receipts/F7-point-float-exact.json
refused: the certificate does not replay exactly: … [rule: receipt: exact replay; scope: characteristic 0]
```

The determinant is 2·10⁻⁹, not 0. Close is not collinear.

## 4. The honest result at 2

Over F₂ the seven points are the seven nonzero vectors of F₂³:

```
gp claim F7-nonempty-2 --matroid F7 --kind NONEMPTY --char 2
gp submit F7-nonempty-2 receipts/F7-point-f2.json            # "characteristic": 2
held: F7-nonempty-2 at characteristic 2

gp claim F7-in-chi-2 --matroid F7 --kind NOT_IN_IDEAL --target 1 --char 2
gp submit F7-in-chi-2 receipts/F7-bridge-2.json              # rule: bridge
held: F7-in-chi-2 at characteristic 2
```

`NOT_IN_IDEAL --target 1` is the statement "realizable over the algebraic closure", which is what p ∈ χ(M) means. The bridge rule turns a point into it.

**χ(F7) = {2} is now fully held:** EMPTY at 0 and at every prime except 2, and realizable at 2.

## 5. Mistake three: "non-Fano is realizable everywhere"

Delete the line {4, 5, 7} and you get the non-Fano plane F7⁻. The same seven vectors, read over ℚ, realize it. One guard, the determinant of {4, 5, 7}, equals 2 there:

```
gp claim F7m-nonempty-2 --matroid F7- --kind NONEMPTY --char 2
gp submit F7m-nonempty-2 receipts/F7m-point-q.json
refused: the certificate reaches 0 and every prime except {2}, which does not cover the
requested characteristic 2 …
```

At 2 the opposite is true. The rational identity `Σ qᵢ·eqᵢ = det(4,5,7)` has residual `2·x4·y5·z7`, which vanishes mod 2. Replay it there with `"characteristic": 2`:

```
gp claim F7m-empty-2 --matroid F7- --kind EMPTY --char 2
gp submit F7m-empty-2 receipts/F7m-empty-mod2.json
held: F7m-empty-2 at characteristic 2
```

## 6. Read the ledger

```
gp status
held     F7m-real-q   NONEMPTY   characteristic 0; earned, unclaimed: 0 and every prime except {2}
...
F7 (modulo ENCODING-FRAME):
  not realizable: held at characteristic 0 and every prime except [2] (F7-empty-outside2)
  realizable (geometrically nonempty): held at characteristic 2 (F7-in-chi-2)
```

- **One honest result:** χ(F7) = {2}, held, modulo the OPEN frame premise. `gp explain F7-in-chi-2` shows the licence tree.
- **One earned-but-unclaimed widening:** `F7m-real-q` claimed only "realizable over ℚ". The same point earns every prime except 2, and GP says so without being asked.
- **One tailing:** `gp tailings --export` keeps the refused "Fano is realizable nowhere" attempt with its reach. The next person who tries it finds the reason already written down.

Notice the shape. Fano: finite, without 0. Non-Fano: cofinite, with 0. That is the Rado–Vámos dichotomy, and nobody told the ledger about it.
