"""Compiler-slot regression probes. Construct text only; never execute it."""
from grandportage import cas

def probe(case,route):
 d=case['inputs']
 try:
  p=cas.CASProgram(cas.SINGULAR,ring=d['ring_name'],ring_vars=d['variables'],decls=[(r['name'],r['type'],r['expression']) for r in d['temporaries']],body=d['statements'],outputs=d['requested_outputs'])
 except (cas.IdentifierCollision,cas.CASError,ValueError,TypeError) as exc:return dict(observed_verdict='REFUSE',reason=str(exc),refused_at='program_construction',external_execution=False)
 return dict(observed_verdict='ACCEPT',reason='Program construction accepted these checked slots; no execution or general grammar-safety proof.',program_text=p.text,external_execution=False)
