# JC p-axis frozen evidence

These fixtures separate three layers:

- `factor_power_v1.json`: standalone exact factor identities;
- `factor_power_affine_contradiction_v1.json`: standalone factor-to-affine
  contradiction pattern;
- `native_axis_slice_v1.json`: frozen, source-fingerprinted JC axis receipt;
- `localized_unit_ideal_v1.json`: the smaller exact certificate to which the
  specialized contradiction compiles.

Only the last certificate already has a graph-authority path, and only after it
is rebound to the exact model and receives a current verifier verdict. The
factor receipts remain independent semantic cross-checks.

The frozen slice binds the 98,779-byte native parent receipt at
`sha256:77a110c9d5fc0ab47c67f86509f3d777d8d9602bad08a992244d3fd98d1b4dde`.
Its own canonical SHA-256 is
`5c682ad0b2f5212fd21aba723d094793a212a1f59654a27b60969a9fa2bf0850`.
