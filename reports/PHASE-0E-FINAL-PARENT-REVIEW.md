# Phase 0e final parent slice: P13/P14/P15 and certificate review

2026-09-29 local; sources inspected 2026-09-30 UTC. Reading-stage proposals only. No installation, import, prototype, source execution or external contact.

## P13 Hets — imitate for M1 only

[The authors' logical-framework paper, section 2.1](https://kwarc.info/people/frabe/Research/CHKMRS_lfhets_11.pdf) separates signatures, sentences, models and satisfaction. A comorphism translates sentences forward and models back, with satisfaction preserved. For GP this sharpens M1: context transport needs an explicit statement map, model map and preservation obligation. A translation name alone supplies none of these. The paper also distinguishes model-theoretic correctness arguments from automatically verified implementation; historical declarative extensions are described, not tested here.

[Codescu's 2019 Hets paper, section 2](https://drops.dagstuhl.de/storage/00lipics/lipics-vol139-calco2019/LIPIcs.CALCO.2019.17/LIPIcs.CALCO.2019.17.pdf) adds a useful warning: translations can introduce target axioms, not merely rename symbols. Those assumptions must remain explicit. Its modal configurations are not automatically GP coefficient fields or campaign states.

Use the semantic discipline in M1; do not adopt institution machinery or user-facing Hets. The original 2007 author PDF returned502; the related primary papers and official Hets documentation supplied this bounded conceptual answer. Current exporter compatibility, licence and deployment are unreviewed because adoption is not proposed.

## P14 AFP algebraic numbers — imitate

The [AFP entry](https://isa-afp.org/entries/Algebraic_Numbers.html) records BSD licensing, rational-coefficient root/factorization support and separate exact versus approximate display. It identifies later improvements in certified factorization and bisection. No package compatibility or execution result follows from the entry.

Selected introduction and Sturm-interface sections of the [254-page proof document](https://isa-afp.org/browser_info/current/AFP/Algebraic_Numbers/document.pdf) show resultants for arithmetic, rational Sturm root counts, factorization to control representative degree and complex numbers represented by real/imaginary components. Endpoint root counting is explicit. Only selected sections were read, not all254pages; older introduction limitations are not a verdict on separate newer AFP entries.

The [Real_Algebraic_Numbers theory](https://isa-afp.org/browser_info/current/AFP/Algebraic_Numbers/Real_Algebraic_Numbers.html), innermost representation and invariant, uses an integer polynomial with rational interval endpoints and exactly one root in the closed interval. Its invariant includes endpoint-sign agreement and polynomial normalization; later layers quotient duplicate representations. A polynomial identity or approximate decimal alone does not identify a selected root.

Proposed receipt obligations: bind polynomial, selected root, exact interval conventions and normalization; validate uniqueness and all model constraints; use exact arithmetic for substitutions and denominator guards. Alternative intervals may denote the same root, so byte inequality is not mathematical inequality. These are GP design inferences, not an adopted Isabelle-to-Lean checker. Restrict representable witnesses to the supported algebraic class; a rational polynomial solution set can contain transcendental points. No new case or general algebra engine is commissioned. Live AFP pages were not immutable byte-pinned or compiled; future component reuse needs exact release/pin and sound binding.

## P15 validated numerics — ignore now, record for post-G5

The [alphaCertified abstract, v2](https://arxiv.org/abs/1011.1091v2) distinguishes square-system convergence certification from heuristic overdetermined validation. The [official Interval overview](https://coqinterval.gitlabpages.inria.fr/) describes Rocq tactics proving bounded real-expression inequalities. These are distinct evidence mechanisms, neither a blanket enumeration/completeness receipt. Only overview/abstract identity was read. Record both for M6 after G5; no deep dive, current compatibility, benchmark, implementation or admission.

## Independent parent intake of P6/P8/P9/P10/P11

The worker's five rows are accepted as bounded primary-source reading, with16actual conservative minutes after corrected completion accounting. Detailed source inspection remains attributed; no native execution was performed.

Parent independently read six pinned files in memory: current polyrith explicitly throws unavailable; the historical Empty Hexagon main file declares the two UNSAT axioms and displays an additional mathlibSorry dependency; Lean's nativeEqTrue adds an axiom and both search/supplied-LRAT paths call it; ETP collects/restricts axioms and marks conjectural evidence; LeanMarathon input metadata binds canonical problem and Lean files. Source hashes and exact links are in the companion JSON. These observations correct the packet's available-polyrith, pure-checker and mandatory three-way-review shortcuts. The origin of mathlibSorry is unreviewed; no claim about every later artifact follows.

The [Flyspeck paper](https://arxiv.org/html/1501.02155), sections5–8, independently confirms historical nonlinear replay costs and the explicit Isabelle-to-HOL Light assumption boundary. Historical compute costs do not predict GP effort.

## Boundary-format corrections

[McKay's graph6 specification](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) encodes an ordered simple undirected graph. graph6 alone is not an isomorphism-canonical labeling or a coverage certificate. Bind any separately computed labeling/permutation and generator coverage.

[DRAT-trim's primary format description](https://github.com/marijnheule/drat-trim/blob/master/README.md) distinguishes the input CNF from the ordered addition/deletion proof. DRAT and LRAT are not interchangeable bytes; any conversion is untrusted elaboration whose output must pass the admitted LRAT route against the exact CNF. Both remain candidate boundary formats; no conversion/checker ran.

All18rows are now accounted for with finite read extents and explicit unknowns. Root PRIOR-ART.md supplies the final bounded synthesis, three recommendations, territory assessment, consumers and corrected interop list. This ends authorized reading rather than proving global novelty or completing G1/G0.

Actual parent charge: 14 minutes; certificate/campaign worker16 minutes; shared total 75/120 minutes. No further reading commissioned.
