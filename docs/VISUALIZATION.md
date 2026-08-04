# Campaign projections and the Three.js explorer

Grand Portage now has a versioned, read-only projection for review tools. The
append-only JSONL graph remains authoritative. A projection is a derived view
and is deliberately rejected as input to the transport kernel.

## Generate the artifacts

```bash
gp project --output campaign.projection.json
gp visualize --output campaign.html --title "Campaign review"
python -m http.server 8000
```

Then open `http://127.0.0.1:8000/campaign.html`. Serving the file over HTTP is
important because browsers apply module restrictions to `file:` URLs.

The JSON output uses schema `grand-portage-projection/v2`. Node records are
references into canonical entries under `collections`, avoiding a second serialized
copy of large model payloads. On the 78-variable JC complete-template assay,
this reduces compact projection JSON from 68,782,731 to 34,393,822 bytes
and the standalone explorer from 68,813,798 to 34,425,501 bytes. A measured
deep polynomial pool would save only about another 1.0 MB, so v2 deliberately
stops at record references. It carries source paths, SHA-256 fingerprints, graph format, kernel epoch, package version, every
folded collection, normalized nodes and normalized relations. Its authority is
always `DERIVED_READ_MODEL_ONLY`.

The HTML embeds that exact JSON snapshot. It does not fetch the campaign, write
to it, accept findings, or feed records back into GP. By default it imports the
pinned Three.js 0.185.1 package from jsDelivr. For an offline or review-pinned
copy, place that same package locally and use, for example:

```bash
gp visualize --output campaign.html --three-root ./vendor/three/
```

Do not mix versions between the core `three` module and `examples/jsm` addons.

## Review packet

Version 0.18 includes a frozen, reproducible exercise packet under
`review/v0.18/`: the JC2 projection, the generated explorer, and commands for
regenerating both from the authoritative fixture. The committed HTML is a
review convenience, not a campaign input, and still carries the projection's
`DERIVED_READ_MODEL_ONLY` marker.

## Reading the explorer

The horizontal layers are semantic roles rather than a force-directed claim
about proof order:

- models;
- transformations (edges, partitions, aliases);
- claims;
- inferences;
- evidence and authority records (certificates, citations, verdicts);
- findings, doubts, notes and tombstones.

Colors identify entity kinds; status accents distinguish declared, verified,
stale/withdrawn and refused/finding states. Click a node to inspect its exact
projected record. Search accepts ids, kinds and record text. Layer toggles,
relation toggles and context dimming make dense campaigns reviewable.

The right panel offers four derived tours:

- **Argument spine** follows inferences in their declared campaign order;
- **Soundness audit** walks checker findings, strongest severities first;
- **Model transformations** follows recorded edges and foregrounds their losses;
- **Claims and certificates** reads each proposition with its scope and evidence.

Each stop frames the selected node, explains the record in plain language, and
keeps its exact JSON below. The narration is generated from projected fields; it
is an orientation aid, not a proof or a new authoritative record. The previous
and next buttons, or `[` and `]`, advance through a tour.

Context depth chooses a one- to four-hop neighborhood. **Focus selected context**
dims everything outside it; **Hide outside context** makes a compact local slice.
Relation-labelled neighbor buttons and Back/Forward preserve an exploration
trail. Selected entities are also written to the URL fragment, so a focused
view can be bookmarked without changing the underlying HTML.

`F` frames the selected node, Escape clears selection, and the mouse or trackpad
orbits, pans and zooms.

## Focused views

```bash
gp project --focus claim:CL-C08 --radius 2 --output c08.json
gp visualize --focus claim:CL-C08 --radius 2 --output c08.html
```

Focus is explicitly an `UNDIRECTED_PRESENTATION_NEIGHBORHOOD`. It is useful for
review, but it is not a dependency theorem and must not be described as a proof
slice. A later dependency projection should be derived from operation contracts
and inference semantics rather than guessed from graph adjacency.

## Design boundary

The projection module depends on folded GP state. The explorer depends only on
the projection schema. This creates a stable seam for future SVG exports,
notebooks, campaign diffs and alternative UIs without giving any of them
mathematical authority. If transport meaning changes, the graph's kernel epoch
still governs compatibility; a visualization schema revision does not mint or
preserve authority by itself.
