"""Calibrate the frozen static architecture checks and prepared README boundary."""
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('replay',ROOT/'tools/check-corpus.py');replay=importlib.util.module_from_spec(spec);spec.loader.exec_module(replay);replay.validate()
spec=importlib.util.spec_from_file_location('architecture_tests',ROOT/'oracle/checkout/tests/test_architecture.py');tests=importlib.util.module_from_spec(spec);spec.loader.exec_module(tests)
records=[]
with TemporaryDirectory(prefix='architecture-probe-',dir=ROOT/'tmp') as tmp:
 p=Path(tmp)/'sample.py'
 for label,source,expected in [('relative','from . import cas\n',{'cas'}),('absolute','import grandportage.cas\n',set()),('dynamic','import importlib\nimportlib.import_module("grandportage.cas")\n',set())]:
  p.write_text(source,encoding='utf-8')
  with patch.object(tests,'PACKAGE',Path(tmp)):actual=tests._local_imports('sample')
  assert actual==expected
  records.append(dict(shape=label,detected=sorted(actual),source_executed=False))
with patch.object(tests,'ROOT',ROOT/'reports/freeze-v0.37.1'):tests.test_readme_remains_a_bounded_introduction()
report=dict(oracle_commit=replay.PIN,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),test_source_sha256=replay.sha(ROOT/'oracle/checkout/tests/test_architecture.py'),records=records,prepared_readme=dict(sha256=replay.sha(ROOT/'reports/freeze-v0.37.1/README.md'),lines=160,actual_frozen_test_passed=True),scope='Static helper sensitivity only; absolute/dynamic samples are parsed but never imported. Passing architecture tests are not a whole-program noninterference proof.')
(ROOT/'reports/ARCHITECTURE-CHECK-BOUNDARIES.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Relative/absolute/dynamic import detection calibrated; actual frozen README limit test passes on the prepared patch.')
