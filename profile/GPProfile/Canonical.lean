import Lean.Data.Json
import GPProfile.Algebra

/-!
Canonical text of statements and scopes (post-G2 §3.1): compact JSON with a fixed key order and
rationals written `num/den`. Binding identities use this text, never `repr`, so a toolchain move
that changes `Repr` or `Format` does not change any binding (G3a review, binder hole b).
-/

namespace GPProfile
open Lean

def ratText (c : Rat) : String := s!"{c.num}/{c.den}"

def sparseCanon (p : Sparse) : Json :=
  Json.arr (p.map fun (e, c) => Json.arr #[toJson e, Json.str (ratText c)]).toArray

def kindCanon : Kind → Json
  | .empty => Json.arr #["EMPTY"]
  | .nonempty => Json.arr #["NONEMPTY"]
  | .inIdeal h => Json.arr #["IN_IDEAL", sparseCanon h]
  | .vanishesOn h => Json.arr #["VANISHES_ON", sparseCanon h]
  | .notInIdeal h => Json.arr #["NOT_IN_IDEAL", sparseCanon h]
  | .cover bs => Json.arr #["COVER", Json.arr (bs.map fun (e, g) =>
      Json.arr #[Json.arr (e.map sparseCanon).toArray, Json.arr (g.map sparseCanon).toArray]).toArray]

/-- The canonical text of a statement: `[vars, eqs, guards, kind]`. -/
def stmtCanon (s : Stmt) : String :=
  (Json.arr #[toJson s.vars, Json.arr (s.eqs.map sparseCanon).toArray,
    Json.arr (s.guards.map sparseCanon).toArray, kindCanon s.kind]).compress

/-- The canonical text of a scope: `[char0, "finite" | "cofinite", primes]`. -/
def scopeCanon (s : Scope) : String :=
  (match s.primes with
    | .finite ps => Json.arr #[toJson s.char0, "finite", toJson ps]
    | .cofinite e => Json.arr #[toJson s.char0, "cofinite", toJson e]).compress

/-- FNV-1a (64-bit) of a byte string: the binder's module fingerprint, computed identically by the
binding export and the runtime. -/
def fnv1a (bs : ByteArray) : UInt64 :=
  bs.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

end GPProfile
