# Regenerable fixture projection reports

Only index.json is retained. Its source and report SHA-256 values use UTF-8
bytes with CRLF normalized to LF. Rebuild with:

    python scripts/project_ir_corpus.py --output tmp/ir-fixture-reports

CI rebuilds these reports; tests compare each generated report hash with this
index. These fixtures are a regression source class, never the decision-bearing
campaign corpus. Use --corpus corpus for that separate, intake-gated experiment.
The original 12k-line report batch has been removed from Git as requested.
