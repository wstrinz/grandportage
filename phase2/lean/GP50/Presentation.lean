import Lean
import GP50.Queries
namespace GP50
open Lean
def stateJson (state : RuntimeState) : Json := Json.mkObj [
  ("status", toJson "OK"), ("held", toJson state.claims),
  ("supports", toJson state.supports), ("domain", toJson state.snapshot.domain),
  ("live_warrants", toJson (eligibleIds state.snapshot)),
  ("warrant_count", toJson state.snapshot.warrants.length),
  ("current_count", toJson state.snapshot.currents.length),
  ("retracted", toJson state.snapshot.retracted), ("successors", toJson state.snapshot.successors)]
def reasonJson : Queries.Reason → Json
  | .inactiveCustody => Json.mkObj [("kind", toJson "inactive_custody")]
  | .refusedOrUnregisteredEvidence => Json.mkObj [("kind", toJson "refused_or_unregistered_evidence")]
  | .missingPremiseRecord id => Json.mkObj [("kind", toJson "missing_premise_record"), ("id", toJson id)]
  | .unsupportedPremise id => Json.mkObj [("kind", toJson "unsupported_premise"), ("id", toJson id)]
def whyNotJson (q : Queries.WhyNot) : Json := Json.mkObj [
  ("claim", toJson q.claim), ("held", toJson q.held),
  ("warrants", toJson (q.warrants.map fun w => Json.mkObj [
    ("id", toJson w.id), ("supported", toJson w.supported),
    ("reasons", toJson (w.reasons.map reasonJson))]))]
def earnedJson (q : Queries.Earned) : Json := Json.mkObj [
  ("claim", toJson q.claim), ("open_obligations", toJson q.openObligations)]
end GP50
