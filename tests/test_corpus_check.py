import json
from scripts import corpus_check as C

def source(tmp_path):
    root=tmp_path/"source"; root.mkdir()
    (root/"graph.jsonl").write_text(json.dumps({"ev":"meta","graph_format":8})+"\n"+
        json.dumps({"ev":"verdict","id":"V","representation":{"proof":1}})+"\n")
    return root

def test_export_is_byte_exact_and_hash_mismatch_refuses(tmp_path):
    src=source(tmp_path); dst=tmp_path/"export"
    C.export(src,dst)
    assert (src/"graph.jsonl").read_bytes()==(dst/"graph.jsonl").read_bytes()
    assert C.validate_campaign(dst)["status"]=="READY"
    with (dst/"graph.jsonl").open("a") as f: f.write('{"ev":"note","invented":true}\n')
    r=C.validate_campaign(dst)
    assert r["status"]=="BLOCKED-ON-CORPUS"
    assert any("SHA mismatch" in s for s in r["reasons"])
    assert any("fields absent" in s for s in r["reasons"])

def test_legacy_and_receiptless_exports_stay_blocked(tmp_path):
    src=source(tmp_path); (src/"graph.jsonl").write_text('{"ev":"meta","graph_format":7}\n')
    dst=tmp_path/"export"; C.export(src,dst)
    r=C.validate_campaign(dst)
    assert len(r["reasons"])==2
    assert C.check(tmp_path/"missing")["status"]=="BLOCKED-ON-CORPUS"

def test_unmanifested_artifact_and_path_escape_are_refused(tmp_path):
    src=source(tmp_path); dst=tmp_path/"export"; C.export(src,dst)
    (dst/"new.json").write_text('{}')
    assert "unmanifested or missing file" in C.validate_campaign(dst)["reasons"]
    p=dst/"export-manifest.json"; m=json.loads(p.read_text())
    m["files"][0]["path"]="../source/graph.jsonl"; p.write_text(json.dumps(m))
    assert "unsafe manifest path" in C.validate_campaign(dst)["reasons"]


def test_rewriting_export_manifest_cannot_reset_the_intake_pin(tmp_path):
    src=source(tmp_path); root=tmp_path/"corpus"; dst=root/"arr15"
    C.export(src,dst)
    baseline=C.check(root); (root/"manifest.json").write_text(json.dumps(baseline))
    p=dst/"export-manifest.json"; m=json.loads(p.read_text())
    m["source"]="different source"; p.write_text(json.dumps(m))
    refused=C.check(root)
    assert "export manifest changed since intake" in refused["campaigns"]["arr15"]["reasons"]
    assert refused["campaigns"]["arr15"]["export_manifest_sha256"]==baseline["campaigns"]["arr15"]["export_manifest_sha256"]
    (root/"manifest.json").write_text(json.dumps(refused))
    assert "export manifest changed since intake" in C.check(root)["campaigns"]["arr15"]["reasons"]
