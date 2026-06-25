<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

Jonathan D.A. Jewell \<[j.d.a.jewell@open.ac](j.d.a.jewell@open.ac).uk\>
:toc: :icons: font

> [!TIP]
> **AI agents:** read `0-AI-MANIFEST.a2ml` first, then
> `.machine_readable/6a2/STATE.a2ml`.

# What This Is

`ideas-to-alphas` is the **incubator** of the hyperpolymath type theory
pipeline: the theory→practice stage where a finding from the **lab**
(`kategoria`) is matured from **idea to alpha** before it earns its own
production (typed) repo.

> [!NOTE]
> This repo is mid-rename. The GitHub repo and local directory are still
> named `kategoria-pipeline` until the owner runs `gh` `repo` `rename`
> `ideas-to-alphas` (+ local `mv`). The role split — **lab** =
> `kategoria` (research/discovery), **incubator** = this repo
> (idea→alpha), **portal** = `nextgen-typing` (front-page on-ramp for
> people) — is captured in
> `dev-notes/2026-06-16-typing-sub-estate-roles-and-lifecycle.adoc`.
> Also update `project` `=` `"katagoria"` → `"ideas-to-alphas"` in
> `.machine_readable/6a2/STATE.a2ml` at rename time.

# Pipeline Position

    katagoria  →  typell  →  typed-wasm  →  PanLL
    (this repo)   (kernel)   (target)    (eNSAID env)

`katagoria` is upstream of everything. Ideas here are **speculative**:
proofs-of-concept, reading notes, prototype Idris2/Lean formalizations.
They graduate to `typell` when they are ready to be integrated into the
production verification kernel.

Coordination monorepo:
[nextgen-typing](https://github.com/hyperpolymath/nextgen-typing)

# What Lives Here

- Type theory prototypes — Idris2, Lean 4, Agda proofs-of-concept

- Research notes on papers being read and formalized

- Experimental level definitions for the TypeLL open-ended progression

- Speculative session type extensions (multi-party, probabilistic,
  temporal)

- Tropical type theory experiments (connections to protocol-squisher)

# What Does NOT Live Here

- Production Rust code — goes in `typell`

- WasmGC type safety proofs — goes in `typed-wasm`

- Anything with stability guarantees — this repo is deliberately
  unstable

# Relationship to TypeLL

TypeLL is an **open-ended progressive** type safety framework. The
current L1-L10 implementation in typell was designed here first, then
graduated. Future levels (L11, L12, …) will originate here before
promotion.

There is no fixed ceiling. katagoria is where the ceiling gets pushed.

# Status

Pre-alpha. Newly created (2026-04-11). Research artefacts will
accumulate over time.

# License

MPL-2.0

Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
\<[j.d.a.jewell@open.ac](j.d.a.jewell@open.ac).uk\>
