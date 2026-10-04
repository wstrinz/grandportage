"""Current algebra boundary probes; no external CAS execution or new kernel code."""
from grandportage import groebner as G, verify as V, operations as O, cas

def decision(ok, reason, **extra):
    return dict(observed_verdict="ACCEPT" if ok else "REFUSE", reason=reason, **extra)

def never(*args, **kwargs):
    raise RuntimeError("Unexpected external CAS call")

def probe(case, route):
    d, action = case["inputs"], route["action"]
    if action == "point":
        values = [G.substitute_polynomial(g, d["variables"], d["point"], d["characteristic"]) for g in d["generators"]]
        point_ok = all(G.parse_polynomial(v,d["variables"],d["characteristic"]).is_zero for v in values)
        if not point_ok:
            raise ValueError("The proposed counterexample does not satisfy the equations")
        return decision(d["attempt"] == "point",
                        "Exact point substitution in the declared characteristic.", substituted=values)
    if action == "substitution":
        try:
            actual=G.substitute_polynomial(d["expression"],d["variables"],d["images"],0)
            receipt=G.check_membership_identity("("+actual+")-("+d["proposed"]+")",[],[],d["variables"],0)
        except G.CertificateError as exc:
            return decision(False,str(exc))
        return decision(True,"Simultaneous substitution matches proposed polynomial.",actual=actual,receipt=receipt)
    if action == "pending":
        from test_operations import _pending_graph
        graph=_pending_graph(O.saturate_closure("M_A","x","M_S",["x","y"],["x*y"]))
        verdict,why=V.identity(graph,"CL",_runner=never)
        return decision(verdict != V.UNVERIFIED,why,raw_verdict=verdict,executed=False)
    if action in ("bounded", "removed", "completeness"):
        from test_adversarial import _op_graph
        graph=_op_graph(d["built_generators"], "Eliminate" if action=="removed" else "SaturateClosure")
        if action == "bounded":
            graph.models["SRC"]["generators"]=d["source_generators"]
            class Backend:
                targets=[]
                def membership(self, ring, target, generators, **kwargs):
                    self.targets.append(target)
                    # Exact monomial divisibility for this one source ideal, not a general solver.
                    p=G.parse_polynomial(target,ring,0)
                    member=all(m[0]>=9 and m[1]>=1 for m in p.terms)
                    return dict(is_member=member,reduced=target,cofactors=["1"] if member else [])
            backend=Backend()
            verdict,why,certificate=V.operation_output(graph,"E",_backend=backend)
            return decision(verdict==V.OP_UNSOUND,"Attempted refutation from bounded search: "+why,
                            raw_verdict=verdict,certificate=certificate,searched_targets=backend.targets,executed=False)
        verdict,why,certificate=V.operation_output(graph,"E",_runner=never)
        if action=="removed":
            return decision(verdict==V.OP_SOUND,why,raw_verdict=verdict,certificate=certificate,executed=False)
        # Empty output passes the one-sided check, yet misses y, whose membership is explicit.
        witness=G.check_membership_identity("x^2*y",graph.models["SRC"]["generators"],["1","0"],["x","y"],0)
        value=G.substitute_polynomial("y",["x","y"],{"x":"1","y":"1"},0)
        incomplete=(not graph.models["SAT"]["generators"] and value=="1")
        return decision(not incomplete,"Empty output omits y although x^2*y belongs to the source ideal; point (1,1) distinguishes them.",
                        raw_verdict=verdict,raw_reason=why,certificate=certificate,missing_generator_witness=witness,executed=False)
    if action == "parse":
        def runner(program, timeout):
            return dict(aborted=False,returncode=0,stderr="",stdout=d["stdout"]+program.completion_marker+"\n")
        backend=cas.SingularBackend(runner=runner,binary_version="test-double")
        try:
            result=backend.factorizing_decomposition(["x"],["x"])
        except cas.CASError as exc:
            return decision(False,str(exc),external_execution=False)
        return decision(True,"Complete producer output parsed; no mathematical authority inferred.",pieces=result,external_execution=False)
    raise ValueError(action)
