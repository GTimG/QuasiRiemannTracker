# Authenticated, append-only registry

`verifications/<sha256-of-canonical-envelope>.json`: every authenticated successful verification receipt, including reruns. `logs/<log-sha256>.log`: complete logs. Import with `node verifier/archive-receipt.mjs RECEIPT LOG` from protected code; commit via maintainer review before publication.

`records/<stable-id>/`: `receipt.json` (the earliest successful archived receipt for this exact revision), `verification.log`, and a separately signed `publication.json` binding independent review, merge/source digests and timestamps.

`events/<sequence>-<digest>.json`: signed append-only withdrawal/supersession events, hash-chained with `previous`. Never edit/delete old entries. Generate from protected code with `verifier/events.mjs`.

`npm run build` authenticates signatures, policy, challenge, source bindings, journal/logs, publication review, chronological lineage and event chain before generating `public/registry.json`. Submitted manifests and PR prose cannot set verification status.

This directory intentionally contains no real records yet. Configure real public keys and complete baseline commissioning before importing anything. Synthetic examples live only in `public/demo-fixtures.json`.
