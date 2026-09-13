import pytest
from grandportage import cas
from tests.test_backend import _program, _raw, _finished

BANNER = "Singular for x86_64-Linux version 4.2.1 (4212, 64 bit)"

def transcript(program, banner=BANNER):
    n=program.completion_nonce
    return _finished(program, "@@GP-ID:"+n+"\n"+banner+"\n@@GP-ID-END:"+n+"\n@@GP_G:\nGP_G[1]=x\n")

def test_native_execution_identity_is_from_that_transcript(monkeypatch):
    monkeypatch.setattr(cas,"_singular_binary_version",lambda:BANNER)
    monkeypatch.setattr(cas,"_run_subprocess",lambda p,t:_raw(transcript(p)))
    backend=cas.SingularBackend(); run=backend.execute(_program())
    assert run.artifact.backend.binary_version==BANNER
    assert 'system("--version");' in run.artifact.program_text
    assert backend.can_record_verdicts
    assert backend.provenance()["binary_version"]==BANNER

@pytest.mark.parametrize("mode",["different","missing","duplicate","wrong_nonce"])
def test_identity_failure_cannot_record(monkeypatch,mode):
    monkeypatch.setattr(cas,"_singular_binary_version",lambda:BANNER)
    def runner(p,t):
        s=transcript(p,BANNER.replace("4.2.1","4.3.1") if mode=="different" else BANNER)
        if mode=="missing": s=_finished(p,"@@GP_G:\nx\n")
        if mode=="duplicate": s=s+s
        if mode=="wrong_nonce": s=s.replace(p.completion_nonce,"0"*32)
        return _raw(s)
    monkeypatch.setattr(cas,"_run_subprocess",runner)
    backend=cas.SingularBackend()
    with pytest.raises(cas.CASError,match="identity"): backend.execute(_program())
    assert len(backend.executions)==1
    assert not backend.can_record_verdicts
    with pytest.raises(cas.CASError,match="mixed backend identity"): backend.provenance()

def test_mixed_trace_cannot_rehabilitate_earlier_execution():
    backend=cas.SingularBackend(runner=lambda p,t:_raw(_finished(p,"@@GP_G:\nx\n")),binary_version="unavailable: earlier")
    earlier=backend.execute(_program())
    backend._binary_version=BANNER
    backend.execute(_program())
    assert earlier.artifact.backend.binary_version=="unavailable: earlier"
    with pytest.raises(cas.CASError,match="mixed backend identity"): backend.provenance()
    assert backend.provenance(1)["binary_version"]==BANNER

@pytest.mark.live
def test_native_inband_version_replays():
    backend=cas.SingularBackend()
    run=backend.execute(_program())
    assert cas._parse_result(run,["GP_G"])["GP_G"]=="GP_G[1]=x"
    assert run.artifact.backend.binary_version==backend.identity.binary_version
    assert backend.can_record_verdicts
