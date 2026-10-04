
"""Index pinned sources and history without claiming semantic review completeness."""
import ast, json, re, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
ORACLE = ROOT/"oracle/checkout"
pin = json.loads((ROOT/"oracle/PIN.json").read_text(encoding="utf-8-sig"))
inventory = json.loads((ROOT/"corpus/SOURCE-INVENTORY.json").read_text(encoding="utf-8-sig"))
tests, hits = [], []
pattern = re.compile(r"confess|counterexample|unsound|trap|regression|false licen[cs]e|wrong|stale|timeout|unverified",re.I)
for item in inventory["sources"]:
    path = ORACLE/item["path"]
    if path.suffix.lower() not in (".py",".md",".lean",".json",".jsonl"):
        continue
    text = path.read_text(encoding="utf-8-sig")
    if item["path"].startswith("tests/") and path.suffix == ".py":
        tree = ast.parse(text,filename=item["path"])
        for node in ast.walk(tree):
            if isinstance(node,(ast.FunctionDef,ast.AsyncFunctionDef)) and node.name.startswith("test_"):
                tests.append({"path":item["path"],"line":node.lineno,"name":node.name,
                              "docstring":ast.get_docstring(node),
                              "assertions":sum(isinstance(n,ast.Assert) for n in ast.walk(node)),
                              "status":"unreviewed"})
    for i,line in enumerate(text.splitlines(),1):
        if pattern.search(line):
            hits.append({"path":item["path"],"line":i,"text":line.strip(),"status":"unreviewed"})
raw = subprocess.check_output(
    ["git","-C",pin["source_path"],"log",pin["commit"],"--format=%H%x09%aI%x09%s"],
    text=True,encoding="utf-8")
history = []
for row in raw.splitlines():
    commit,date,title = row.split("\t",2)
    history.append({"commit":commit,"date":date,"title":title,
                    "candidate":bool(pattern.search(title) or re.search(r"fix|repair|retract|errat|revert|supersed|mismatch|scope",title,re.I)),
                    "status":"unreviewed"})
out = ROOT/"corpus/index"
out.mkdir(exist_ok=True)
for name,records in [("TESTS",tests),("SOURCE-HITS",hits),("HISTORY",history)]:
    (out/(name+".json")).write_text(json.dumps(
        {"schema_version":1,"source_commit":pin["commit"],
         "notice":"Mechanical discovery index; records are candidates, not reviewed incidents or extracted cases.",
         "records":records},indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
print(json.dumps({"test_functions":len(tests),"source_hits":len(hits),"commits":len(history),
                  "history_candidates":sum(c["candidate"] for c in history)}))
