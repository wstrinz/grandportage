"""Verify the private doc-only freeze package without modifying either source repo."""
from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[1]; O=ROOT/'oracle/checkout'; P=ROOT/'reports/freeze-v0.37.1'; OLD=(Path(__import__('os').environ.get('GP_DEV_ROOT') or Path.home()/'dev'))/'grand-portage'
def git(root,*args):return subprocess.check_output(['git','-c','safe.directory='+root.as_posix(),'-C',str(root),*args])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pin=json.loads((ROOT/'oracle/PIN.json').read_text(encoding='utf-8'))
commit=git(O,'rev-parse','HEAD').decode().strip()
assert commit=='ac4155787207e2847d248cffed7be871d5dcd577'
assert not git(O,'status','--porcelain','--untracked-files=no').strip()
ref=git(OLD,'rev-parse','refs/tags/v0.37.0').decode().strip();target=git(OLD,'rev-parse','v0.37.0^{commit}').decode().strip();assert target==commit
tag=git(OLD,'cat-file','-p','refs/tags/v0.37.0').decode()
banner='> *Frozen at v0.37.0. This repository remains the reference implementation and fixture source for a successor now in design. No further feature development here.*'
readme=(P/'README.md').read_text(encoding='utf-8');original=(O/'README.md').read_text(encoding='utf-8')
assert readme.splitlines()[0]==banner and original.count('â€”')==17 and 'â€”' not in readme
assert len(readme.splitlines()) <= 160, 'Prepared README exceeds the frozen architecture test limit'
spec=(P/'SPEC.md').read_text(encoding='utf-8');status=spec.split('## Status\n',1)[1].split('\n## ',1)[0]
assert 'graph format 8, kernel epoch 12' in status and 'eleven live user sessions' not in status and 'graph format 7' not in status and 'kernel epoch 11' not in status
fmt=(O/'grandportage/format.py').read_text(encoding='utf-8');assert 'GRAPH_FORMAT = 8' in fmt and 'KERNEL_EPOCH = 12' in fmt
assert '__version__ = "0.37.0"' in (O/'grandportage/__init__.py').read_text(encoding='utf-8')
paths=['README.md','SPEC.md','review/v0.37/KNOWN-ISSUES.md'];patch=P/'freeze-docs.patch'
changed=re.findall(r'^\+\+\+ b/(.+)$',patch.read_text(encoding='utf-8'),re.M);assert changed==paths
with tempfile.TemporaryDirectory(prefix='freeze-apply-',dir=ROOT/'tmp') as scratch:
 root=Path(scratch);git(root,'init','-q')
 for p in paths[:2]:(root/p).write_bytes((O/p).read_bytes())
 git(root,'apply','--check',str(patch));git(root,'apply',str(patch))
 for p in paths:assert (root/p).read_bytes()==(P/p).read_bytes(),p
# Use the frozen publication policy to classify the tree plus proposed documentation.
sp=importlib.util.spec_from_file_location('snapshot',O/'scripts/public_snapshot.py');module=importlib.util.module_from_spec(sp);sp.loader.exec_module(module)
manifest=module.load_manifest(O/'public-snapshot-v1.json');tracked=git(O,'ls-tree','-r','--name-only','HEAD').decode().splitlines();classified=module.classify_paths(manifest,sorted(set(tracked+paths)))
assert all(p in classified['public'] for p in paths)
# Relative Markdown links in the prepared entry documents must not lead to private content.
link_checks=[]
for p in paths:
 text=(P/p).read_text(encoding='utf-8')
 for target in re.findall(r'\]\(([^)]+)\)',text):
  if '://' in target or target.startswith('#'):continue
  target=target.split('#')[0]
  private=target in manifest['private_paths'] or any(target.startswith(x) for x in manifest['private_prefixes'])
  assert not private,(p,target)
  link_checks.append(dict(source=p,target=target))
assert 'HISTORY/ (private workspace archive; unavailable in the public snapshot)' in readme
assert 'private workspace only' in spec and '`KILL-CRITERIA.md`' in spec
known=(P/paths[-1]).read_text(encoding='utf-8')
for text in ['Radical membership earns point','not a reproduced end-to-end false-authority result','p-integral unit-ideal certificate','p-integral rational witness','open-locus guards']:assert text in known
assert not git(O,'status','--porcelain','--untracked-files=no').strip()
assert git(OLD,'rev-parse','refs/tags/v0.37.0').decode().strip()==ref
report=dict(oracle_commit=commit,script_sha256=sha(Path(__file__)),patch_sha256=sha(patch),files=[dict(path=p,sha256=sha(P/p)) for p in paths],existing_tag=dict(name='v0.37.0',object=ref,commit=target,annotation=tag.split('\n\n',1)[1].strip(),freeze_annotation_present=False,modified=False),checks=dict(verbatim_banner=True,readme_lines=len(readme.splitlines()),readme_limit=160,mojibake_repairs=17,status_matches_runtime_constants=True,doc_only_paths=paths,isolated_git_apply_check=True,applied_bytes_match_prepared_files=True,publication_policy_classifies_patch_public=True,prepared_entry_document_private_links_absent=True,known_issues_preserve_advice_vs_authority_distinction=True,oracle_unchanged=True),link_checks=link_checks,scope='Private preparation verified. Not applied to original/oracle; no tag changed; no public release or new test-suite run.',remaining='User-approved public application/publication, if requested. Preserve existing v0.37.0 tag target; do not force-retag. Freeze designation is in the prepared README banner.')
(P/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print('Freeze package verified: 3 documentation files, 17 encoding repairs, exact banner, current constants, isolated patch application and unchanged release tag.')
