# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

- `npm install` — installs deps AND runs `scripts/copy-vendor-files.js` via `postinstall` to copy Z3 WASM + COI service worker into `public/`. You must re-run `npm install` (or the script directly) if `public/z3-built.js`, `public/z3-built.wasm`, or `public/coi-serviceworker.js` are missing — they are gitignored.
- `npm run dev` — Vite dev server. `vite.config.js` sets COOP/COEP headers (`same-origin` / `credentialless`) that are required for `SharedArrayBuffer` (which Z3's threaded WASM needs).
- `npm run build` — produces `dist/`. Per the README, `dist/` is committed and served directly on GitHub Pages (note: `.gitignore` lists `/dist/` but the README treats it as tracked — confirm before committing build output).
- `npm run preview` — preview the built bundle.

No test suite, linter, or formatter is configured.

## Architecture

Browser-only vanilla-JS ES-module app. No framework, no bundler beyond Vite, no server-side code.

### Pipeline (`js/app.js`)

`SolverApp` orchestrates a 5-step flow that makes **three separate LLM calls per solve cycle**:

1. NL problem → SMT-LIB (`translateToSmtLib`)
2. SMT-LIB → NL verification, shown to user (`verifySmtLib`)
3. User clicks Solve → Z3 WASM runs (`Z3Solver.solve`)
4. If `sat`: raw model + original problem → NL solution (`translateSolution`)
5. If `unsat`: extract unsat-core names, feed with original problem + SMT-LIB → NL explanation (`explainUnsat`)

The `translateToSmtLib` system prompt enforces conventions the rest of the pipeline depends on: `(set-option :produce-unsat-cores true)`, every assertion wrapped in `(! … :named kebab-case-name)`, ending with `(check-sat)` only. If you change that prompt, the unsat-core extraction and explanation path will break.

### Z3 integration (`js/z3solver.js`)

Two non-obvious constraints shape this file:

- **Global init handshake.** `index.html` loads the vendored `z3-built.js` as a classic `<script>` *before* the module graph, which sets `globalThis.initZ3`. It also polyfills `window.global = globalThis` because `z3-solver` expects Node's `global`. `Z3Solver._doInit` then calls `init` from `z3-solver/build/browser.js`, polling up to 10s for `globalThis.initZ3` to appear.
- **Two-phase solve on a fresh context.** `solve()` strips any `(get-model)` / `(get-unsat-core)` from the input, evaluates constraints + `(check-sat)` first, parses the result, and only then issues `(get-model)` or `(get-unsat-core)` against the **same** context. A fresh context (`mk_config` / `mk_context`, with the old one `del_context`'d) is created per call to prevent state leaks between solves. Do not collapse this into a single `eval_smtlib2_string` — the conditional follow-up on the same context is what makes both sat-model and unsat-core paths work.

### LLM client (`js/OpenRouterAPI.js`)

Thin wrapper over OpenRouter's OpenAI-compatible `/chat/completions`. Default model `anthropic/claude-haiku-4.5`, configurable in the UI. The API key is **kept in memory only** (never written to localStorage); only the model name is persisted. Verbose request/response logging to `console` is intentional for debugging the prompt round-trip — do not strip it without a reason.

### Vendor-file copy step (`scripts/copy-vendor-files.js`)

Copies three files from `node_modules` into `public/` so Vite serves them same-origin (required under COEP):

- `z3-solver/build/z3-built.js` → `public/z3-built.js`
- `z3-solver/build/z3-built.wasm` → `public/z3-built.wasm`
- `coi-serviceworker/coi-serviceworker.js` → `public/coi-serviceworker.js`

The service worker is what lets the built app run on hosts like GitHub Pages that can't set COOP/COEP response headers — it re-registers requests with the right headers client-side. First load on such hosts triggers a one-time reload.
