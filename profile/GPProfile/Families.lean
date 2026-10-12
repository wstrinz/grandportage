import GPProfile.Families.Extension
import GPProfile.Families.Surface

/-!
Family adapters of the shared case-to-profile frontend (post-G2 §1.8). Each adapter reads one
input family of the v0.37-derived corpus and builds a `Plan` of profile inputs only. Families
are recognized by their input keys; none is keyed to a case id. A case no family recognizes is
an expressiveness loss.
-/

namespace GPProfile.Families
open Lean GPProfile

/-- Dispatch on input keys. -/
def plan (case : Json) (params : List (String × Nat)) : Except String Plan := do
  let inputs ← case.getObjVal? "inputs"
  let elabOr (r : Except String Plan) : Except String Plan :=
    match r with
    | .ok p => .ok p
    | .error e =>
      if e.startsWith "undeclared variable" || e.startsWith "incomplete map" ||
          e.startsWith "undefined map" then
        .ok { items := [], requested := [], elaboration := some e }
      else .error e
  let k := onlyKeys inputs
  if has inputs "membership_target" && k ["variables", "generators", "guards", "numerator",
      "denominator_powers", "localization_powers", "membership_target", "cofactors", "coefficient_field",
      "point_universe", "chart", "cite", "proposed_change", "parent_generators", "characteristic"] &&
      (str? inputs "point_universe" |>.all (· == "ALGEBRAIC_CLOSURE")) &&
      ((obj? inputs "proposed_change").all fun c => onlyKeys c ["generators", "open_conditions", "chart", "cite", "point_universe"] || c == .null) then
    return ← localizedFamily inputs
  if has inputs "model" && k ["model", "identity", "cofactors", "local_backend", "historical_identity",
      "raw_artifact", "question"] && questionIs inputs ["exact_identity_current"] &&
      (obj? inputs "model").all modelOk && nestedOk inputs "identity" ["left", "right"] then
    return ← modelIdentity inputs
  if k ["lhs", "rhs", "variables", "characteristic"] && has inputs "lhs" then
    return ← ambientFamily inputs
  if has inputs "power_identity" && k ["variables", "characteristic", "declared_units", "exponent_limit",
      "power_identity", "question"] && questionIs inputs ["check_power_identity"] &&
      nestedOk inputs "power_identity" ["equation", "scalar", "base", "exponent"] &&
      (← scalarOk inputs ((obj? inputs "power_identity").bind (str? · "scalar"))) then
    return ← ambientFamily inputs
  if (obj? inputs "identity").any (fun j => has j "equation") && k ["variables", "characteristic",
      "declared_units", "identity", "parent_equations", "open_guards", "question"] &&
      questionIs inputs ["check_identity"] && has inputs "question" &&
      nestedOk inputs "identity" ["equation", "scalar", "left", "right"] &&
      (← scalarOk inputs ((obj? inputs "identity").bind (str? · "scalar"))) then
    return ← ambientFamily inputs
  if has inputs "images" && k ["variables", "expression", "images", "proposed"] then
    return ← elabOr (substitution inputs)
  if has inputs "point_forward" && k ["source", "target", "point_forward", "point_inverse",
      "target_pullback_rows", "source_pullback_rows", "question"] &&
      (obj? inputs "source").all modelOk && (obj? inputs "target").all modelOk then
    return ← ringMapFamily inputs
  if has inputs "forward_cofactors" && k ["variables", "generators", "forward", "inverse",
      "forward_cofactors", "inverse_cofactors"] then
    return ← ringMapFamily inputs
  if has inputs "target_ideal" && k ["variables", "source_ideal", "target_ideal", "identity", "origin",
      "point", "point_containment_proof", "identity_difference", "target_cofactors"] then
    return ← elabOr (idealsFamily inputs)
  if has inputs "nonzero_guards" && k ["coefficient_domain", "point_universe", "variables", "equations",
      "nonzero_guards", "point"] && (str? inputs "point_universe").all (· == "rational points") then
    return ← pointFamily inputs
  if (has inputs "target_variables" && k ["source_variables", "target_variables", "identity"]) ||
      (has inputs "eliminated" && k ["built_generators", "eliminated"]) then
    return ← elabOr (eliminationFamily inputs)
  if has inputs "excluded_fiber_generators" && k ["variables", "parent_equations", "excluded_base",
      "excluded_fiber_generators", "parent_point"] then
    return ← fiberFamily inputs
  if k ["variables", "equations", "point"] && has inputs "point" && has inputs "equations" then
    return ← displayedPointFamily inputs
  if has inputs "source_universe" && k ["variables", "generators", "coefficient_domain", "source_universe",
      "target_universe"] && str? inputs "coefficient_domain" == some "Q" then
    return ← elabOr (universesFamily inputs)
  if has inputs "region" && k ["variables", "equations", "region", "predicate"] then
    return ← regionalFamily inputs
  if has inputs "claims" && k ["claims", "requested"] then
    return ← elabOr (surfaceFamily inputs)
  if has inputs "searched_exponents" && k ["built_generators", "source_generators", "searched_exponents"] then
    return ← searchFamily inputs
  if has inputs "field_polynomial" && k ["variables", "generators", "guards", "point_universe",
      "field_polynomial", "coordinate", "proposed_change"] &&
      (str? inputs "point_universe" |>.all (· == "ALGEBRAIC_CLOSURE")) &&
      ((obj? inputs "proposed_change").all fun c =>
        c == .null || (match c with | .arr _ => true | _ => false) ||
        onlyKeys c ["generators", "open_conditions", "point_universe", "verifier_version"]) then
    return ← elabOr (extensionWitnessFamily inputs)
  -- The combinatorial context keys (object, vertices, classes, edges) describe the system only.
  if has inputs "witness_field" && k ["object", "vertices", "classes", "edges", "coefficient_domain",
      "point_universe", "variables", "equations", "point", "witness_field", "nonzero_guards",
      "interpretation_limit"] &&
      str? inputs "coefficient_domain" == some "Q" && str? inputs "point_universe" == some "ALGEBRAIC_CLOSURE" &&
      nestedOk inputs "witness_field" ["kind", "base", "symbol", "minimal_polynomial"] &&
      (obj? inputs "witness_field").any (fun w => str? w "kind" == some "simple_number_field_v1" &&
        str? w "base" == some "Q") then
    return ← extensionPointFamily inputs
  if has inputs "cancelled_conclusion" && k ["variables", "product", "cancelled_conclusion", "point",
      "unit_witness"] then
    return ← cancelFamily inputs
  if has inputs "source_predicate" && k ["control", "source_point", "target_point", "forward", "backward",
      "source_predicate"] && (str? inputs "control").any (["backward_rewrite", "wrong_forward_rewrite"].contains ·) then
    return ← translationFamily inputs
  if has inputs "element" && k ["variables", "generators", "element", "annihilator", "cofactors",
      "nonzero_point", "zero_point"] then
    return ← elementFamily case inputs
  if has inputs "branches" && k ["parent", "branches"] && (obj? inputs "parent").all modelOk &&
      (match obj? inputs "branches" with | some (.arr bs) => bs.all modelOk | _ => false) then
    return ← coverFamily inputs
  if has inputs "attempt" && k ["variables", "generators", "characteristic", "point", "attempt"] then
    return ← attemptFamily inputs case
  if let some (.arr ids) := obj? inputs "identity" then
    if k ["identity", "source_context", "target_context"] then
      -- An identity written in one context and copied into another context's signature.
      let sides ← ids.toList.mapM text
      let vars := (sides.flatMap identifiers).eraseDups
      let (scope, field) ← scopeField inputs
      return ← ambient vars (sides.getD 0 "0") (sides.getD 1 "0") scope field
  if k legacyKeys then
    return ← elabOr (do let i ← frontend case params; pure (single i.stmt i.scope (.receipt i.cert)))
  throw "inputs fit no 3a frontend family"

end GPProfile.Families
