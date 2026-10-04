"""Generate metadata-only contract-layer tags; never execute or rewrite cases."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

LAYERS = ("kernel", "profile", "adapter", "surface", "host")
REPO = Path(__file__).resolve().parents[1]
POLICY_VERSION = "phase2-full-contract-layers-v2"

def decision(layer, rationale, candidates=None, review_group="unreviewed", secondary_duties=None):
    candidates = list(candidates or ([layer] if layer else LAYERS))
    duties = list(secondary_duties or [])
    return {
        "primary_layer": layer, "candidate_layers": candidates,
        "g2_kernel_eligible": (layer == "kernel") if layer else (None if "kernel" in candidates else False),
        "status": "resolved" if layer else "unresolved", "rationale": rationale,
        "review_group": review_group, "full_contract_required": True,
        "secondary_layers": [d["layer"] for d in duties], "secondary_duties": duties,
    }

def catalog():
    # Explicit reviewed ID groups, based on FULL unchanged contracts.
    # No numeric default: an absent ID always remains unresolved.
    rows = {}
    def put(ids, layer, review_group, rationale, secondary_duties):
        for ident in ids.split():
            if ident in rows:
                raise ValueError(f"duplicate reviewed case: {ident}")
            rows[ident] = decision(layer, rationale, review_group=review_group,
                                   secondary_duties=secondary_duties)
    put("GP-A01 GP-A08a GP-A14 GP-A15 GP-A16-covered GP-A16-missing GP-A17 GP-A18 GP-A25a GP-A25b GP-A26 GP-C03 GP-A27-drop-GRH GP-A27-full GP-A27-heuristic GP-A27-keep-GRH GP-A27-label GP-A27-partial GP-X04 GP-X09 GP-X14 GP-X60 GP-X61 GP-X62 GP-X65 GP-X82 GP-X173 GP-X174 GP-X176 GP-X177 GP-X178 GP-X179 GP-X180 GP-X183 GP-X184 GP-X186 GP-X229 GP-X283 GP-X399 GP-X402 GP-X403", "kernel", "supplied-premise-authority",
        "The full fixture assumes mathematical premises or supplies only declaration/claim data; registered rule, exact context, dependency and scope obligations decide authority.", [])
    put("GP-X142 GP-X143 GP-X144 GP-X145 GP-X146 GP-X147 GP-X148 GP-X149 GP-X150 GP-X151 GP-X152 GP-X153 GP-X154 GP-X155 GP-X156 GP-X157 GP-X158 GP-X159 GP-X160 GP-X161 GP-X162 GP-X163 GP-X164 GP-X165 GP-X166 GP-X167 GP-X168 GP-X169 GP-X170 GP-X171 GP-X172", "kernel", "native-event-lifecycle",
        "The complete fixture tests typed event declarations, independent checked support, targeted retraction/supersession and current snapshot provenance.", [])
    put("GP-A19 GP-A20a GP-C04", "adapter", "cas-language",
        "The complete contract requires faithful CAS program construction or supported expression grammar.", [{"layer":"kernel","duty":"Bind the constructed expression to the declared model without granting authority from producer text."}])
    put("GP-X35 GP-X36 GP-X37 GP-X38 GP-X39 GP-X40 GP-X41 GP-X42 GP-X43 GP-X44 GP-X100 GP-X101 GP-X102 GP-X103 GP-X104 GP-X105 GP-X106 GP-X107 GP-X108 GP-X109 GP-X110 GP-X111 GP-X112 GP-X113 GP-X114 GP-X115 GP-X116 GP-X97 GP-X98 GP-X99", "adapter", "frozen-report-contract",
        "The fixture mutates a supplied frozen report or its exact source/byte bindings and licenses; enforce the complete report contract and retained scope.", [{"layer":"kernel","duty":"Retain named premises, scope, unresolved branches and input/receipt identity; report labels cannot mint support."},{"layer":"profile","duty":"Interpret the report's declared mathematical objects, universes and region limits faithfully; no broader mathematical result is licensed."}])
    put("GP-X72 GP-X131 GP-X139 GP-X140 GP-X199 GP-X200 GP-X281 GP-X282 GP-X294 GP-X295 GP-X329 GP-X337 GP-X338 GP-X344 GP-X346 GP-X370 GP-X371 GP-X372 GP-X373 GP-X379 GP-X385 GP-X387 GP-X390 GP-X391 GP-X392 GP-X393 GP-X394 GP-X395 GP-X396 GP-X400", "adapter", "encoding-and-admission-boundaries",
        "The full fixture requires exact decoder, export, legacy migration, transcript snapshot or dispatch behavior; an abstract binding check cannot pass it.", [{"layer":"kernel","duty":"Preserve typed declaration, bound execution/model identity and missing-support debt across this boundary."}])
    put("GP-X201 GP-X202 GP-X203 GP-X204 GP-X205 GP-X206 GP-X207 GP-X208 GP-X209 GP-X210 GP-X240 GP-X241 GP-X242 GP-X243 GP-X244 GP-X245 GP-X246 GP-X247 GP-X248 GP-X249 GP-X250 GP-X251 GP-X252 GP-X253 GP-X254", "adapter", "producer-protocol-and-grammar",
        "Parse the complete identity/completion envelope or construct the complete protected CAS slot grammar; producer completion alone creates no theorem.", [{"layer":"kernel","duty":"Keep producer identity/completion separate from admitted checked evidence and held claims."}])
    put("GP-X302 GP-X303 GP-X304 GP-X305 GP-X306 GP-X307", "adapter", "canonical-composition-export",
        "The complete contract requires canonical intermediate exports and their composed algebraic replay.", [{"layer":"profile","duty":"Check both exact coefficient/Laurent algebra passes and the intermediate mathematical object."},{"layer":"kernel","duty":"Bind both checked legs to the same intermediate object before any composed authority."}])
    put("GP-X211 GP-X212 GP-X213 GP-X214 GP-X215 GP-X216 GP-X217 GP-X218 GP-X219 GP-X220 GP-X221 GP-X226 GP-X227 GP-X230 GP-X231 GP-X232 GP-X233 GP-X234 GP-X235 GP-X236 GP-X237 GP-X238 GP-X239 GP-X375 GP-X376 GP-X380 GP-X381 GP-X382 GP-X383 GP-X384", "host", "storage-process-and-filesystem",
        "The complete fixture requires actual storage, path/publication, process/recording or request transaction behavior.", [{"layer":"adapter","duty":"Preserve canonical artifact/transcript bytes and structured operation records at the host boundary."},{"layer":"kernel","duty":"Host success or retained bytes alone do not create a mathematical claim; preserve bound evidence identity."}])
    put("GP-X181 GP-X182 GP-X185 GP-X187 GP-X188 GP-X189 GP-X190 GP-X191 GP-X192 GP-X374 GP-X377 GP-X378 GP-X386 GP-X388 GP-X389 GP-X397 GP-X398", "surface", "audit-and-consumer-projection",
        "The full fixture requires honest audit/check/render, warning continuation, frontier status or structured consumer response behavior.", [{"layer":"kernel","duty":"Preserve missing premises, live construction dependencies, meaning bindings and unknown-status debt in the reported state."}])
    put("GP-X01 GP-X02 GP-X03 GP-X05 GP-X06 GP-X07 GP-X08 GP-X10 GP-X11 GP-X12 GP-X13 GP-X15 GP-X16 GP-X17 GP-X18 GP-X19 GP-X20 GP-X21 GP-X22 GP-X23 GP-X24 GP-X25 GP-X26 GP-X27 GP-X28 GP-X29 GP-X30 GP-X31 GP-X32 GP-X33 GP-X34", "profile", "elementary-algebra-and-transport",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X45 GP-X46 GP-X47 GP-X48 GP-X49 GP-X50 GP-X51 GP-X52 GP-X53 GP-X54 GP-X55 GP-X56 GP-X57 GP-X58 GP-X59 GP-X63 GP-X64 GP-X66 GP-X67 GP-X68 GP-X69 GP-X70 GP-X71 GP-X73 GP-X74 GP-X75 GP-X76 GP-X77 GP-X78 GP-X79 GP-X80 GP-X81 GP-X83 GP-X84 GP-X85 GP-X86 GP-X87 GP-X88 GP-X89 GP-X90 GP-X91 GP-X92 GP-X93 GP-X94 GP-X95 GP-X96", "profile", "native-point-chain-and-cover-replay",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X117 GP-X118 GP-X119 GP-X120 GP-X121 GP-X122 GP-X123 GP-X124 GP-X125 GP-X126 GP-X127 GP-X128 GP-X129 GP-X130 GP-X132 GP-X133 GP-X134 GP-X135 GP-X136 GP-X137 GP-X138 GP-X141", "profile", "exact-counterexample-and-substitution",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X193", "kernel", "finite-recorded-use-coverage",
        "Finite recorded-use coverage is incomplete independently on both asserted dimensions: place t and orders -4, 0, 1, 2 are missing. No mathematical universe completeness or arithmetic replay is requested.", [])
    put("GP-X194", "kernel", "finite-recorded-use-coverage",
        "The supplied inventory covers place t but still omits recorded construction order -4 and conclusion orders 0, 1, 2; repairing one dimension does not discharge the other.", [])
    put("GP-X195", "kernel", "finite-recorded-use-coverage",
        "All supplied recorded order uses are represented, but place t is still missing; complete coverage requires each asserted dimension independently.", [])
    put("GP-X196", "kernel", "finite-recorded-use-coverage",
        "Every supplied construction and conclusion use is represented on both asserted dimensions. This finite obligation coverage does not prove mathematical constraint strength or universe completeness.", [])
    put("GP-X197", "kernel", "finite-recorded-use-coverage",
        "Both supplied recorded-use lists are empty, so finite recorded-use coverage has no detected gap. This does not certify that all real-world or mathematical uses were recorded.", [])
    put("GP-X198", "kernel", "finite-recorded-use-coverage",
        "The supplied conclusion-only order 0 requires representation even without an order construction use; place coverage cannot discharge that missing conclusion obligation.", [])
    put("GP-X175", "kernel", "stored-certificate-binding",
        "The supplied success sequence and stored proof mutation require stale binding refusal; the fixture contains no polynomial or cofactor rows to replay.",
        [{"layer": "profile", "duty": "Validate the mathematical content of any replacement section certificate before admitting a new bound success; no replacement is supplied here."}])
    put("GP-X222 GP-X223 GP-X224 GP-X225 GP-X228", "profile", "self-contained-cofactor-replay",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X255 GP-X256 GP-X257 GP-X258 GP-X259 GP-X260 GP-X261 GP-X262 GP-X263 GP-X264 GP-X265 GP-X266 GP-X267 GP-X268 GP-X269 GP-X270 GP-X271 GP-X272 GP-X273 GP-X274 GP-X275 GP-X276 GP-X277 GP-X278 GP-X279 GP-X280 GP-X284 GP-X285 GP-X286 GP-X287 GP-X288 GP-X289 GP-X290 GP-X291 GP-X292 GP-X293 GP-X296 GP-X297 GP-X298 GP-X299 GP-X300 GP-X301", "profile", "section-map-cover-and-pattern",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X308 GP-X309 GP-X310 GP-X311 GP-X312 GP-X313 GP-X314 GP-X315 GP-X316 GP-X317 GP-X318 GP-X319 GP-X320 GP-X321 GP-X322 GP-X323 GP-X324 GP-X325 GP-X326 GP-X327 GP-X328 GP-X330 GP-X331 GP-X332 GP-X333 GP-X334 GP-X335 GP-X336 GP-X339 GP-X340 GP-X341 GP-X342 GP-X343 GP-X345 GP-X347 GP-X348 GP-X349 GP-X350 GP-X351 GP-X352 GP-X353 GP-X354 GP-X355 GP-X356 GP-X357 GP-X358 GP-X359 GP-X360 GP-X361 GP-X362 GP-X363 GP-X364 GP-X365 GP-X366 GP-X367 GP-X368 GP-X369", "profile", "sos-matrix-recurrence-and-number-field",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-X401 GP-X404 GP-X405 GP-X406 GP-X407 GP-X408 GP-X409 GP-X410 GP-X411 GP-X412", "profile", "family-root-and-point-validation",
        "The complete unchanged fixture requires mathematical interpretation, exact arithmetic/certificate replay, point/cover validation or a concrete mathematical counterexample.", [{"layer":"kernel","duty":"Bind admitted results to their exact model, context, premises and scope; an identity-only refusal is not a complete fixture pass."}])
    put("GP-A02 GP-A03a GP-A03b GP-A04 GP-A05 GP-A06 GP-A07a GP-A07b GP-A08b GP-A08c GP-A09 GP-A10-C GP-A10-Q GP-A10-R GP-A11a GP-A11b GP-A12 GP-A13-ambient GP-A13-derived GP-A20b GP-A21 GP-A22 GP-A23 GP-A24 GP-C01 GP-C02", "profile", "base-mathematical-language",
        "The complete fixture requires mathematical statement, region, expression equality or certificate semantics.", [{"layer":"kernel","duty":"Preserve context, object identity and scope when admitting the mathematical result."}])
    put("GP-X413 GP-X414 GP-X415", "profile", "base-mathematical-language",
        "The complete fixture requires mathematical statement, region, expression equality or certificate semantics.", [{"layer":"kernel","duty":"Preserve context, object identity and scope when admitting the mathematical result."}])
    return rows

CATALOG = catalog()

def read_cases(case_dir: Path):
    result = []
    seen = set()
    for path in sorted(case_dir.glob("*.json")):
        raw = path.read_bytes()
        case = json.loads(raw.decode("utf-8-sig"))
        if not isinstance(case, dict):
            raise ValueError(f"case must be an object: {path.name}")
        ident = case.get("id")
        if not isinstance(ident, str) or not ident or ident in seen:
            raise ValueError(f"invalid/duplicate case id in {path.name}: {ident!r}")
        if path.stem != ident:
            raise ValueError(f"case id does not match filename: {path.name}")
        seen.add(ident)
        result.append((path, case, hashlib.sha256(raw).hexdigest()))
    return result

def generate(case_dir: Path, expected_count=None):
    cases = read_cases(case_dir)
    if expected_count is not None and len(cases) != expected_count:
        raise ValueError(f"expected {expected_count} cases, found {len(cases)}")
    rows = []
    for path, case, digest in cases:
        tagging = CATALOG.get(case["id"], decision(
            None, "Case is outside the finite reviewed catalog; Will must decide layer and possible G2 eligibility."))
        rows.append({
            "id": case["id"], "path": f"corpus/must/{path.name}", "sha256": digest,
            **tagging, "evidence_pointers": ["/title", "/inputs", "/attempted_conclusion", "/expected/reason"],
        })
    return {"schema_version": 1, "policy_version": POLICY_VERSION,
            "case_count": len(rows), "cases": rows}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--case-dir", type=Path, default=REPO / "corpus/must")
    p.add_argument("--output", type=Path, default=REPO / "corpus/LAYER-TAGS.json")
    args = p.parse_args()
    data = generate(args.case_dir, expected_count=462)
    args.output.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"tagged {data['case_count']} unchanged cases -> {args.output}")
if __name__ == "__main__":
    main()
