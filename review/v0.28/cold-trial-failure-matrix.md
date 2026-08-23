# Attempt log and failure matrix

Cycle start (UTC): `2026-08-23T16:02:39.0737098+00:00`.
Cycle finish (UTC): `2026-08-23T16:24:32.4468340+00:00`.
Elapsed wall time: `1313.373 s` (`00:21:53.373`).

This is an honest record of the single bounded attempt. No Grand Portage
surface was used; graph effect is `NONE`. No campaign search universe was
generated or widened.

| Event (verbatim diagnostic where applicable) | Proposed classification | Effect / disposition |
|---|---|---|
| Requested base was `628c24e`, but preflight found HEAD `49de799697b91e212570cfeadf865cc2c8a0579a` and pre-existing modifications in seven packet-owned paths. | `OUT_OF_BAND_CONTAMINATION` / `BASE_MISMATCH` | Did not reset or overwrite wholesale. Confirmed HEAD descends from the requested base; audited the base-bound inputs and preserved the coordinator corrections. |
| `warning: unable to access 'C:\Users\wstri/.config/git/ignore': Permission denied` | `ENVIRONMENT_WARNING` | Repeated on Git reads; non-blocking and did not change evidence. |
| First JSON summary assumed generic matrix/count keys and printed null values. | `OPERATOR_MISREADING` | Re-read the actual schema and used `explicit_witness_matrix_k1_embedding`, `replay_all_four_embeddings`, and the documented geometry files. |
| A broad automorphism JSON read emitted the 600-element list and was truncated. | `WRONG_TOOL_SCOPE` | Re-ran a keys/count-only inspection; no inference depended on truncated output. |
| Two web calls returned no visible material because the wrapper incorrectly inspected `result.content` although the tool returned a string. | `WRONG_TOOL_CALL_HANDLING` | Corrected by serializing the complete result. |
| Direct arXiv HTML/cache requests returned 404/cache misses. | `PRIMARY_TEXT_ACCESS_STALL` | Used the locally pinned Barakat–Kühne primary extraction; left inaccessible sources `PACKET_ONLY`. |
| The official Terao PDF was exposed as an iframe/text page, and PDF screenshot failed because the response was not `application/pdf`. | `PRIMARY_TEXT_ACCESS_STALL` | Citation located, but full text not inspected; retained `PACKET_ONLY`. |
| Cuntz supplement click/open failed through the web cache/safe-URL route. | `SUPPLEMENT_ACCESS_STALL` | Tried a read-only shell fetch. |
| `Invoke-WebRequest`: `An attempt was made to access a socket in a way forbidden by its access permissions.` | `SANDBOX_NETWORK_REFUSAL` | Re-ran the same read-only fetch with approved escalation, as required by the environment instructions. |
| Three read-only network fetches were approved outside the sandbox; no files were written. | `OUT_OF_BAND_PERMISSION_INTERVENTION` | First obtained the supplement, second parsed all entries, third isolated candidate entries. This was permission mediation, not mathematical coaching. |
| The first successful supplement fetch used a badly scoped `Select-String` and dumped a very large, truncated response. | `WRONG_TOOL_SCOPE` | Replaced with structural parsing and compact summaries. |
| PowerShell reported `ParserError: Missing 'in' after variable in foreach loop` in a follow-up histogram command. | `OPERATOR_SYNTAX_ERROR` | Corrected spacing and reran successfully. |
| The first mandated replay returned: `C:\Users\wstri\AppData\Local\Programs\Python\Python310\python.exe: can't open file 'C:\\Users\\wstri\\dev\\math-research\\campaigns\\arr15\\artifacts\\publication-positioning\\replay.py': [Errno 2] No such file or directory` | `MISSING_REQUIRED_ARTIFACT` | Added the bounded stdlib replay surface and reran it in this cycle. |
| The added replay found: `base digest mismatch: RESULTS_SO_FAR.md: declared=f15ac92092a24014a1413909966632559dc998d36377de8af9ae2a26c9d53290 actual=384681f801f5197b4cb9a82b7f09d68e07808446cc27da48eba7ebddc0db1ead`. The other five declared base-input digests match exactly. | `PACKET_INPUT_DIGEST_MISMATCH` | Did not substitute or waive the declared digest. Replay continues through all artifact and mutation checks, then exits nonzero with `FAIL_PACKET_INPUT_MISMATCH`. |
| The second replay used the wrong expected stdout phrase (`Total affine labeling witnesses found`) for a script that actually prints `satisfying all 25 constraints: 100`, and stopped with `REPLAY_STATUS=FAIL: affine witness count mismatch`. | `OPERATOR_REPLAY_ASSERTION_ERROR` | Corrected the literal assertion to the script's deterministic wording; the mathematical count was 100 throughout. |
| Bresciani full-text routes returned cache misses/403; only abstracts were readable. | `PRIMARY_TEXT_ACCESS_STALL` | No object-specific cohomology/descent claim promoted; status remains `PACKET_ONLY`. |
| No campaign hook was invoked, so there was no hook refusal. | `HOOK_REFUSAL_NONE` | Nothing to report beyond the explicit absence. |

No human or agent supplied mid-cycle coaching. The only intervention was the
environment's explicit approval of read-only network access after the
sandbox refused the same request.
