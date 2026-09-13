import json
from grandportage import cli, store as S

def test_lint_warns_without_writing_or_refusing(tmp_path,capsys):
    root=str(tmp_path)
    S.append([{"ev":"model","id":"M","field":"Q"},
              {"ev":"claim","id":"P","model":"M","kind":"PREDICATE","statement":"prose only"}],root)
    path=tmp_path/".portage/graph.jsonl"; before=path.read_bytes()
    assert cli.main(["--root",root,"lint","--json"])==0
    data=json.loads(capsys.readouterr().out)
    assert data["warnings"][0]["claim"]=="P"
    assert data["graph_effect"]=="NONE"
    assert path.read_bytes()==before
