"""Reproduce harmless comments being mistaken for division by the frozen compiler."""
from pathlib import Path
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
from grandportage import cas
records=[]
for label,body,accept in [('assignment',['I = std(I);'],True),('comment_only',['// harmless comment'],False),('comment_and_assignment',['// harmless comment','I = std(I);'],False),('nonconstant_division',['I = I/x;'],False)]:
 cas.assert_declares_nothing(cas.SINGULAR,body,'body')
 try:
  p=cas.CASProgram(cas.SINGULAR,ring='R',ring_vars=['x'],decls=[('I','ideal','x')],body=body,outputs=['I']);actual=True;error=None
 except cas.CASError as exc:actual=False;error=str(exc)
 assert actual==accept
 records.append(dict(control=label,statement_guard_accepted=True,program_constructed=actual,error=error))
report=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_sha256=replay.sha(ROOT/'oracle/checkout/grandportage/cas.py'),records=records,finding='Harmless Singular // comments are accepted by the statement guard but rejected when the subsequent scalar-division guard parses raw comments as Python expressions.',classification='conservative refusal, no false authority',proposal='Use a shared lexer or typed syntax representation so comments and strings are distinguished from arithmetic before division validation. Preserve division and identifier controls; naive stripping is not a general parser proof.',changed_expected_verdicts=False,external_execution=False)
(ROOT/'reports/COMMENT-DIVISION-AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Four compiler controls reproduced: assignment accepted, two harmless comment forms refused, actual nonconstant division still refused.')
