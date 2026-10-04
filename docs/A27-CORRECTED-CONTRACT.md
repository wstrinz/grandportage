# A27 corrected contract fixtures

Basis: approved revision-3 amendments in DECISIONS.md and reports/PACKET-REV3-REVIEW.md. These are conditional admission/scope fixtures, not real class-group computations or captured certifying runs. No checker is admitted by this document. The explicit supplied premises may be exercised later using an abstract profile; they do not require implementing number theory in the kernel.

## Source correction

Current PARI bnfinit documentation supports a GRH-conditional computation, not the packet's blanket claim that the present default is heuristic under GRH. Full bnfcertify(bnf,0) success and partial bnfcertify(bnf,1) success have different conclusions. Magma Proof=Full must be interpreted with its effective global class-group bound. These documented semantics motivate the contract below; no actual PARI or Magma invocation is asserted.

Sources checked in the approved packet review: https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html (bnfinit/bnfcertify); https://magma.maths.usyd.edu.au/magma/handbook/text/416 (ClassGroup Proof and SetClassGroupBounds). Historical default behavior is not used as a present-day fixture. Version strings below identify only synthetic contract data, never a real tool release.

## Fixed expectations

- A27-heuristic: an explicitly heuristic assertion without an admitted successful check cannot establish a complete class group, even when GRH is assumed. REFUSE.
- A27-drop-GRH: a checked full-result premise whose reach requires GRH cannot become unconditional. REFUSE.
- A27-keep-GRH: the same checked full-result premise can support the same bound claim under GRH. ACCEPT, conditional on the supplied admission/check premises.
- A27-partial: a checked quotient-of-candidate conclusion does not establish candidate equals the full class group. REFUSE.
- A27-full: a checked full-result premise with unconditional reach supports the same bound unconditional claim. ACCEPT, conditional on the supplied admission/check premises.
- A27-label: a producer's full-certification label without an admitted checker result cannot establish the claim. REFUSE.

## Input and interpretation boundary

Every fixture binds the same exact number-field presentation Q[a]/(a^2+5), proposed group invariant factors [2], and claim payload by SHA-256. Synthetic producer/checker contract versions and effective assumptions are explicit. The asserted positive premises say that an admitted checker has already successfully checked the bound claim; no receipt bytes, checker implementation, theorem, class-group computation or proof of these premises is supplied. Consequently these are rule-level conditional controls only, not end-to-end acceptance tests. They must not be described as replayed arithmetic or admitted authority in this workspace.

The expected result depends on those premises and their scope, not on the fact that the example class-group value might independently be true. The partial case supplies only a quotient relation: a quotient of a candidate group need not equal it. The heuristic and label controls supply no admitted proof at all. Dropping GRH is invalid even if this particular example can separately be proved unconditionally.

## Frozen oracle disposition

All six cases are UNSUPPORTED by the selected v0.37 oracle projection. Its affine claim/reach and certificate registry does not implement this class-group receipt plus explicit-GRH contract. No fabricated native ACCEPT/REFUSE is produced. Generic PREDICATE prose or an unknown certificate refusal would test a different contract. Retain these fixed expectations for later abstract-profile/binding tests and present this expressiveness limit explicitly at closeout. A future real arithmetic adapter would need concrete checked evidence before minting a warrant; these fixtures do not authorize that adapter or waive checker admission.
