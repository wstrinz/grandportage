"""Inventory repository graph fixtures; write reports only, never graph files."""
import argparse
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from grandportage import project_v2 as I
from grandportage import store as S
from grandportage import format as F
from grandportage import kernel as K


def event_files():
    for base in ("fixtures", "tests/fixtures", "examples"):
        for path in sorted((ROOT/base).rglob("*")):
            if path.suffix not in (".json", ".jsonl"):
                continue
            try:
                text = path.read_text(encoding="utf-8")
                if path.suffix == ".jsonl":
                    data = [json.loads(line) for line in text.splitlines()
                            if line.strip() and not line.lstrip().startswith("#")]
                else:
                    data = json.loads(text)
                    if isinstance(data, dict):
                        data = data.get("events", [])
                if isinstance(data, list) and any(isinstance(e, dict) and e.get("ev") in
                        ("model", "claim", "meta") for e in data):
                    yield path, data, "stored events (no inferred meta or context)"
            except (ValueError, OSError):
                continue


def wrapped_fixtures():
    for name in ("class_12909_open_witness.json", "class_4102.json"):
        path = ROOT / "tests/fixtures/arr15" / name
        data = json.loads(path.read_text(encoding="utf-8"))
        # Only package the literal mathematical fields. Do not invent about,
        # characteristic, point universe, or a statement beyond the fixture.
        model = {k: data[k] for k in ("ring_vars", "generators", "open_conditions")}
        yield path, [F.meta_event(), dict(model, ev="model", id="fixture-model")], (
            "ARR15 model payload wrapper; synthetic id/meta only; no invented claim or field context")
    path = ROOT / "tests/fixtures/atlas/ordered_certificate.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    yield path, [F.meta_event(), dict(data["model"], ev="model", id="atlas-model"),
                 {"ev": "claim", "id": "atlas-empty", "model": "atlas-model", "kind": "EMPTY",
                  "statement": "the ordered sample has no root", "scope": "ANY_ORDERED",
                  "certificate": "ORDERED_SOS_CERT"}], (
        "atlas sample packaging; explicit fixture context; supplied certificate is unverified data, not a receipt")
    # Retain a literal existing Cloquet regression, not a new foreign-domain study.
    path = ROOT / "tests/test_match4_hardening.py"
    module = ast.parse(path.read_text(encoding="utf-8"))
    fn = next(n for n in module.body if isinstance(n, ast.FunctionDef) and
              n.name == "test_review_is_the_cold_reader_safe_full_history_surface")
    call = next(n for n in ast.walk(fn) if isinstance(n, ast.Call) and
                isinstance(n.func, ast.Attribute) and n.func.attr == "append")
    class Constants(ast.NodeTransformer):
        def visit_Attribute(self, node):
            if isinstance(node.value, ast.Name) and node.value.id == "K":
                return ast.copy_location(ast.Constant(getattr(K, node.attr)), node)
            return node
    events = ast.literal_eval(Constants().visit(call.args[0]))
    yield path, [F.meta_event()] + events, (
        "Cloquet/Match4 existing literal regression; not a complete campaign ledger")


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    manifest, counts, reasons = [], {}, Counter()
    tag_count = tag_total = 0
    stop = False
    for path, events, adapter in list(event_files()) + list(wrapped_fixtures()):
        relative = path.relative_to(ROOT).as_posix()
        name = relative.replace("/", "__").replace(".jsonl", "").replace(".json", "").replace(".py", "") + ".json"
        source = {"path": relative, "sha256": hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
                  "hash_encoding": "source bytes with CRLF normalized to LF", "adapter": adapter}
        try:
            # A portable historical fold deliberately does not probe a local CAS.
            # It is not advertised as a fresh native execution audit.
            legacy = not events or events[0].get("ev") != "meta"
            folded = [F.import_epoch0_event(e) for e in events] if legacy else events
            graph = S.Graph(check_binary_version=False).apply_all(
                [(event, relative, i) for i, event in enumerate(folded, 1)]).validate()
            report = I.project(graph, source)
            report["native_binary_identity_rechecked"] = False
            for category, tally in report["counts"].items():
                counts.setdefault(category, Counter()).update(tally)
            reasons.update(report["reason_counts"])
            tag_count += report["profile_from_tag"]["count"]
            tag_total += report["profile_from_tag"]["denominator"]
            stop |= report["stop_for_missing_context"]
        except (S.GraphError, K.ScopeError, ValueError, KeyError, TypeError) as exc:
            report = {"schema": I.SCHEMA, "source": source, "authority": I.AUTHORITY,
                      "graph_effect": "NONE", "status": "UNPROJECTABLE",
                      "missing": ["loadable_graph"], "load_error": str(exc)}
        (output/name).write_text(json.dumps(report, sort_keys=True, indent=2) + "\n", encoding="utf-8")
        manifest.append({"source": relative, "source_sha256": source["sha256"], "report_sha256": hashlib.sha256((output/name).read_bytes().replace(b"\r\n",b"\n")).hexdigest(), "report": name, "status": report.get("status", "MEASURED"),
                         "source_graph_format": report.get("source_graph_format"),
                         "counts": report.get("counts", {}),
                         "missing_model_context_fraction": report.get("missing_model_context_fraction")})
    summary = {"schema": I.SCHEMA, "authority": I.AUTHORITY, "graph_effect": "NONE", "sources": manifest,
               "counts": {k: dict(v) for k,v in counts.items()}, "reason_counts": dict(reasons.most_common()),
               "profile_from_tag": {"count": tag_count, "denominator": tag_total,
                                    "rate": tag_count/tag_total if tag_total else None},
               "stop_condition": "MISSING_CONTEXT_ABOVE_10_PERCENT" if stop else None,
               "recommendation": None if stop else "NOT_EVALUATED",
               "coverage_limit": "all stored event fixtures plus two ARR15 payloads, the atlas sample, and one existing Cloquet regression; no private sibling campaign graphs imported"}
    (output/"index.json").write_text(json.dumps(summary, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k:v for k,v in summary.items() if k != "sources"}, indent=2))


def run_campaign_corpus(corpus_root, output):
    """Decision-bearing corpus is validated separately, never merged with fixtures."""
    from scripts import corpus_check
    from grandportage import explain as EX, check as C
    intake=corpus_check.check(corpus_root)
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    report={"source_class":"campaign-corpus", "status":intake["status"],
            "authority":I.AUTHORITY,"graph_effect":"NONE", "campaigns":{}, "recommendation":None}
    if intake["status"] != "READY":
        report["reason"]="BLOCKED-ON-CORPUS: require eligible verbatim format-8 exports with retained receipts; migrated/replayed copies are separate recovery evidence"
    else:
        for campaign in corpus_check.CAMPAIGNS:
            graph=S.load(str(Path(corpus_root)/campaign/"graph.jsonl"))
            clean=list(C.clean_inferences(graph,C.run(graph)))
            clean.extend(cid for cid in graph.claims if any(EX._current(graph,rid,v)[0] and
                         str(v.get("verdict", "")).startswith("VERIFIED") for rid,v in EX._receipts(graph,cid)))
            clean=sorted(set(clean))
            explanations=[EX.explain(graph,node) for node in clean]
            per_obligation={name:Counter() for name in EX.OBLIGATIONS};data_gaps=Counter();examples={}
            def visit(tree):
                for name,ob in tree["obligations"].items():
                    per_obligation[name][ob["status"]]+=1
                    if ob["status"]=="DATA_GAP":
                        data_gaps[ob["missing"]]+=1;examples.setdefault(ob["missing"],tree["id"])
                for child in tree["children"]:visit(child)
            for explanation in explanations:visit(explanation["tree"])
            predicates=[c for c in graph.claims.values() if c.get("kind")==K.PREDICATE and not c.get("superseded_by")]
            tagged_receipts=[(rid,v) for rid,v in graph.verdicts.items() if graph.claims.get(v.get("of"),{}).get("certificate")]
            from_tag=sum(not (EX._current(graph,rid,v)[0] and v.get("verifier")=="verify.ordered_sos"
                         and v.get("verifier_version")==1 and v.get("verdict")=="VERIFIED"
                         and isinstance(v.get("representation"),dict)
                         and set(v["representation"])=={"method","ring_vars","generators","squares","cofactors"})
                         for rid,v in tagged_receipts)
            report["campaigns"][campaign]={"licensed_conclusions":len(clean),
                "reconstructed":sum(e["tree"]["complete"] for e in explanations),
                "reconstructed_fraction":sum(e["tree"]["complete"] for e in explanations)/len(clean) if clean else None,
                "obligations":{k:dict(v) for k,v in per_obligation.items()},
                "data_gaps":[{"datum":k,"count":v,"example":examples[k]} for k,v in data_gaps.most_common()],
                "prose_predicate":{"count":sum(c.get("condition") is None for c in predicates),"denominator":len(predicates)},
                "profile_from_tag_receipts":{"count":from_tag,"denominator":len(tagged_receipts)}}
    (output/"corpus-report.json").write_text(json.dumps(report,sort_keys=True,indent=2)+"\n",encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, help="validate and measure campaign exports separately from fixtures")
    parser.add_argument("--output", type=Path, default=ROOT/"review/ir-v2-projection")
    args=parser.parse_args()
    if args.corpus:
        print(json.dumps(run_campaign_corpus(args.corpus,args.output),indent=2))
    else:
        run(args.output)
